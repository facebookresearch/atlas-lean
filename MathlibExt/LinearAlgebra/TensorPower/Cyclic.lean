/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import MathlibExt.Logic.Equiv.Fin.Rotate
public import Mathlib.RepresentationTheory.Basic
public import MathlibExt.LinearAlgebra.TensorPower.Cons

/-!
# Cyclic rotations, representations and norms of tensor powers

For a commutative semiring and a semimodule, the permutation rotating
the last factor of `M^⊗(n+1)` to the first gives a linear equivalence
`ρ_n` with `ρ_n^(n+1)=id`. Over a commutative ring, the signed rotation
`t_n=(-1)^nρ_n` also satisfies `t_n^(n+1)=id` and defines an action
of the cyclic group `ℤ/(n+1)`. Its norm is the finite sum
`N_n=∑_(j=0)^n t_n^j`, satisfying `(1−t_n)N_n=N_n(1−t_n)=0`.

Applying the same linear map to all factors intertwines the rotations,
cyclic actions and norms. The separate-first-factor presentation
`M ⊗[k] M^⊗n` has the same operators through its canonical tensor-word
identification. Pure-tensor formulas specify the inverse permutation
for rotation and the forward permutation for inverse action.

## References

* J.-L. Loday, *Cyclic Homology*, §2.1, for the cyclic operator and norm identities.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w

namespace TensorPower

/-- For `n ∈ ℕ`, the cyclic permutation of `Fin(n+1)` satisfies
`finRotate(n+1)^(n+1)=id`. -/
theorem rotationIndex_period (n : ℕ) : finRotate (n + 1) ^ (n + 1) = 1 :=
  finRotate_pow_succ n

section Unsigned

variable (k : Type u) (M : Type v) [CommSemiring k] [AddCommMonoid M] [Module k M]

/-- Let `k` be a commutative semiring and `M` a `k`-semimodule
with an additive commutative monoid structure. The last-to-first reindexing of `M^⊗(n+1)` is a
linear
equivalence `ρ_n`. -/
def rotation (n : ℕ) : TensorPower k (n + 1) M ≃ₗ[k] TensorPower k (n + 1) M :=
  PiTensorProduct.reindex k (fun _ : Fin (n + 1) => M) (finRotate (n + 1))

/-- Let `k` be a commutative semiring and `M` a `k`-semimodule
with an additive commutative monoid structure. For `a : Fin(n+1) → M`, last-to-first rotation sends
`tprod(a)` to `tprod(i ↦ a(finRotate(n+1)⁻¹(i)))`. -/
@[simp]
theorem rotation_tprod (n : ℕ) (a : Fin (n + 1) → M) :
    rotation k M n (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k (fun i => a ((finRotate (n + 1)).symm i)) :=
  PiTensorProduct.reindex_tprod _ _

/-- Let `k` be a commutative semiring and `M` a `k`-semimodule
with an additive commutative monoid structure. The `j`-th power of the tensor rotation is reindexing
by `finRotate(n+1)^j`. -/
theorem rotation_pow (n j : ℕ) :
    rotation k M n ^ j =
      PiTensorProduct.reindex k (fun _ : Fin (n + 1) => M) (finRotate (n + 1) ^ j) := by
  induction j with
  | zero =>
    change LinearEquiv.refl k _ =
      PiTensorProduct.reindex k (fun _ : Fin (n + 1) => M) (Equiv.refl _)
    exact PiTensorProduct.reindex_refl.symm
  | succ j ih =>
    calc
      rotation k M n ^ (j + 1) = (rotation k M n ^ j).trans (rotation k M n) := by
        rw [pow_succ', LinearEquiv.mul_eq_trans]
      _ = (PiTensorProduct.reindex k (fun _ : Fin (n + 1) => M)
          (finRotate (n + 1) ^ j)).trans
          (PiTensorProduct.reindex k (fun _ : Fin (n + 1) => M) (finRotate (n + 1))) := by
        rw [ih]
        rfl
      _ = PiTensorProduct.reindex k (fun _ : Fin (n + 1) => M)
          ((finRotate (n + 1) ^ j).trans (finRotate (n + 1))) :=
        PiTensorProduct.reindex_trans _ _
      _ = PiTensorProduct.reindex k (fun _ : Fin (n + 1) => M)
          (finRotate (n + 1) ^ (j + 1)) := by
        rw [pow_succ', Equiv.Perm.mul_def]

/-- Let `k` be a commutative semiring and `M` a `k`-semimodule
with an additive commutative monoid structure. On `M^⊗(n+1)`, the unsigned rotation satisfies
`ρ_n^(n+1)=id`. -/
theorem rotation_period (n : ℕ) : rotation k M n ^ (n + 1) = 1 := by
  rw [rotation_pow, rotationIndex_period]
  change PiTensorProduct.reindex k (fun _ : Fin (n + 1) => M) (Equiv.refl _) =
    LinearEquiv.refl k _
  exact PiTensorProduct.reindex_refl

variable {k M} {N : Type w} [AddCommMonoid N] [Module k N]

/-- Let `k` be a commutative semiring and `M` a `k`-semimodule
with an additive commutative monoid structure. For a linear map `f : M → M′`, its map on all factors
commutes with last-to-first rotation in every degree `n`. -/
theorem rotation_natural (f : M →ₗ[k] N) (n : ℕ) (x : TensorPower k (n + 1) M) :
    PiTensorProduct.map (fun _ : Fin (n + 1) => f) (rotation k M n x) =
      rotation k N n (PiTensorProduct.map (fun _ : Fin (n + 1) => f) x) :=
  PiTensorProduct.map_reindex (fun _ : Fin (n + 1) => f) (finRotate (n + 1)) x

end Unsigned

section Signed

variable (k : Type u) (M : Type v) [CommRing k] [AddCommGroup M] [Module k M]

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. The signed last-to-first operator is a linear equivalence
of `T_n`. -/
def cyclicEquiv (n : ℕ) : TensorPower k (n + 1) M ≃ₗ[k] TensorPower k (n + 1) M :=
  LinearEquiv.smulOfUnit ((-1 : kˣ) ^ n) * rotation k M n

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. The signed linear equivalence has value
`t_n(x)=(-1)^n • ρ_n(x)` for every `x : T_n`. -/
theorem cyclicEquiv_apply (n : ℕ) (x : TensorPower k (n + 1) M) :
    cyclicEquiv k M n x = (-1 : k) ^ n • rotation k M n x := by
  change ((↑((-1 : kˣ) ^ n) : k) • rotation k M n x) = _
  simp only [Units.val_pow_eq_pow_val, Units.coe_neg_one]

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. On a pure word, `t_n(tprod(a))` is
`(-1)^n • tprod(i ↦ a(finRotate(n+1)⁻¹(i)))`. -/
@[simp]
theorem cyclicEquiv_tprod (n : ℕ) (a : Fin (n + 1) → M) :
    cyclicEquiv k M n (PiTensorProduct.tprod k a) =
      (-1 : k) ^ n •
        PiTensorProduct.tprod k (fun i => a ((finRotate (n + 1)).symm i)) := by
  rw [cyclicEquiv_apply, rotation_tprod]

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. The signed equivalence satisfies `t_n^(n+1)=id`, since
the accumulated sign has even exponent `n(n+1)`. -/
theorem cyclicEquiv_period (n : ℕ) : cyclicEquiv k M n ^ (n + 1) = 1 := by
  let s : TensorPower k (n + 1) M ≃ₗ[k] TensorPower k (n + 1) M :=
    LinearEquiv.smulOfUnit ((-1 : kˣ) ^ n)
  let r := rotation k M n
  have hsr : Commute s r := by
    change s * r = r * s
    apply LinearEquiv.ext
    intro x
    change (↑((-1 : kˣ) ^ n) : k) • r x = r ((↑((-1 : kˣ) ^ n) : k) • x)
    exact (r.map_smul _ _).symm
  have hs : s ^ (n + 1) = 1 := by
    have hsign : ((-1 : kˣ) ^ n) ^ (n + 1) = 1 := by
      rw [← pow_mul]
      exact (Nat.even_mul_succ_self n).neg_one_pow
    change (DistribMulAction.toModuleAut k (TensorPower k (n + 1) M)
      ((-1 : kˣ) ^ n)) ^ (n + 1) = 1
    rw [← map_pow, hsign, map_one]
  change (s * r) ^ (n + 1) = 1
  rw [hsr.mul_pow, hs]
  have hOne : (1 : TensorPower k (n + 1) M ≃ₗ[k] TensorPower k (n + 1) M) *
      r ^ (n + 1) = r ^ (n + 1) := _root_.one_mul (r ^ (n + 1))
  have hPeriod : r ^ (n + 1) =
      (1 : TensorPower k (n + 1) M ≃ₗ[k] TensorPower k (n + 1) M) :=
    rotation_period k M n
  exact hOne.trans hPeriod

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. In degree zero the signed equivalence on the one-factor
tensor power is identity. -/
@[simp]
theorem cyclicEquiv_zero : cyclicEquiv k M 0 = 1 := by
  simpa only [Nat.zero_add, pow_one] using cyclicEquiv_period k M 0

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. The underlying linear endomorphism of the signed cyclic
equivalence is the cyclic operator on `T_n`. -/
def cyclicOperator (n : ℕ) : Module.End k (TensorPower k (n + 1) M) :=
  (cyclicEquiv k M n).toLinearMap

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. The cyclic endomorphism sends `tprod(a)` to
`(-1)^n • tprod(i ↦ a(finRotate(n+1)⁻¹(i)))`. -/
@[simp]
theorem cyclicOperator_tprod (n : ℕ) (a : Fin (n + 1) → M) :
    cyclicOperator k M n (PiTensorProduct.tprod k a) =
      (-1 : k) ^ n •
        PiTensorProduct.tprod k (fun i => a ((finRotate (n + 1)).symm i)) :=
  cyclicEquiv_tprod k M n a

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. The cyclic endomorphism satisfies `t_n^(n+1)=id`. -/
theorem cyclicOperator_period (n : ℕ) : cyclicOperator k M n ^ (n + 1) = 1 := by
  change (LinearEquiv.automorphismGroup.toLinearMapMonoidHom
    (cyclicEquiv k M n)) ^ (n + 1) = 1
  rw [← map_pow, cyclicEquiv_period, map_one]

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. The cyclic endomorphism in degree zero is identity on the
one-factor tensor power. -/
@[simp]
theorem cyclicOperator_zero : cyclicOperator k M 0 = 1 := by
  change (cyclicEquiv k M 0).toLinearMap = _
  rw [cyclicEquiv_zero]
  rfl

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. Write `C_(n+1)=ℤ/(n+1)` for the additive cyclic group. Integer powers of
the signed equivalence give a group
homomorphism from `C_(n+1)` to linear automorphisms of `T_n`. -/
def cyclicAutomorphism (n : ℕ) :
    Multiplicative (ZMod (n + 1)) →*
      (TensorPower k (n + 1) M ≃ₗ[k] TensorPower k (n + 1) M) :=
  AddMonoidHom.toMultiplicativeLeft <|
    ZMod.lift (n + 1) ⟨{
      toFun j := Additive.ofMul (cyclicEquiv k M n ^ j)
      map_zero' := by
        change cyclicEquiv k M n ^ (0 : ℤ) = 1
        exact zpow_zero _
      map_add' a b := by
        change cyclicEquiv k M n ^ (a + b) =
          cyclicEquiv k M n ^ a * cyclicEquiv k M n ^ b
        exact zpow_add _ _ _ }, by
      change cyclicEquiv k M n ^ ((n + 1 : ℕ) : ℤ) = 1
      simpa only [zpow_natCast] using cyclicEquiv_period k M n⟩

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. Write `C_(n+1)=ℤ/(n+1)` for the additive cyclic group. For `j ∈ ℤ`, the
automorphism associated to its residue
class `[j]` is the signed equivalence raised to `j`. -/
@[simp]
theorem cyclicAutomorphism_intCast (n : ℕ) (j : ℤ) :
    cyclicAutomorphism k M n (Multiplicative.ofAdd (j : ZMod (n + 1))) =
      cyclicEquiv k M n ^ j := by
  change Additive.toMul
    (ZMod.lift (n + 1)
      (A := Additive (TensorPower k (n + 1) M ≃ₗ[k] TensorPower k (n + 1) M))
      _ (j : ZMod (n + 1))) = _
  rw [ZMod.lift_coe]
  rfl

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. Write `C_(n+1)=ℤ/(n+1)` for the additive cyclic group. The residue class
`[1]` acts by the signed linear
equivalence `t_n`. -/
@[simp]
theorem cyclicAutomorphism_generator (n : ℕ) :
    cyclicAutomorphism k M n (Multiplicative.ofAdd (1 : ZMod (n + 1))) =
      cyclicEquiv k M n := by
  simpa only [Int.cast_one, zpow_one] using cyclicAutomorphism_intCast k M n 1

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. Write `C_(n+1)=ℤ/(n+1)` for the additive cyclic group. The signed action
defines a linear representation of
`C_(n+1)` on the tensor power `T_n`. -/
def cyclicRepresentation (n : ℕ) :
    Representation k (Multiplicative (ZMod (n + 1))) (TensorPower k (n + 1) M) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (cyclicAutomorphism k M n)

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. Write `C_(n+1)=ℤ/(n+1)` for the additive cyclic group. For `j ∈ ℕ`, the
representation value at `[j]` is the
endomorphism power `t_n^j`. -/
@[simp]
theorem cyclicRepresentation_natCast (n j : ℕ) :
    cyclicRepresentation k M n (Multiplicative.ofAdd (j : ZMod (n + 1))) =
      cyclicOperator k M n ^ j := by
  have h := cyclicAutomorphism_intCast k M n (j : ℤ)
  simp only [Int.cast_natCast, zpow_natCast] at h
  change LinearEquiv.automorphismGroup.toLinearMapMonoidHom
    (cyclicAutomorphism k M n (Multiplicative.ofAdd (j : ZMod (n + 1)))) = _
  rw [h, map_pow]
  rfl

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. Write `C_(n+1)=ℤ/(n+1)` for the additive cyclic group. The cyclic
representation takes its generator `[1]`
to the cyclic endomorphism `t_n`. -/
@[simp]
theorem cyclicRepresentation_generator (n : ℕ) :
    cyclicRepresentation k M n (Multiplicative.ofAdd (1 : ZMod (n + 1))) =
      cyclicOperator k M n := by
  simpa only [Nat.cast_one, pow_one] using cyclicRepresentation_natCast k M n 1

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. Define `N_n=∑_(j=0)^n t_n^j`. The finite sum `N_n` is the cyclic norm
endomorphism
of `T_n`. -/
def norm (n : ℕ) : Module.End k (TensorPower k (n + 1) M) :=
  ∑ j ∈ Finset.range (n + 1), cyclicOperator k M n ^ j

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. Write `C_(n+1)=ℤ/(n+1)` for the additive cyclic group. The geometric sum
`∑_(j=0)^n t_n^j` equals the finite-group
norm of the cyclic representation. -/
theorem norm_eq_representation_norm (n : ℕ) :
    norm k M n = (cyclicRepresentation k M n).norm := by
  classical
  let e : Fin (n + 1) ≃ Multiplicative (ZMod (n + 1)) :=
    (ZMod.finEquiv (n + 1)).toEquiv.trans Multiplicative.ofAdd
  have he (i : Fin (n + 1)) :
      e i = Multiplicative.ofAdd (i.val : ZMod (n + 1)) := by
    change Multiplicative.ofAdd ((ZMod.finEquiv (n + 1)) i) = _
    exact congrArg Multiplicative.ofAdd
      (ZMod.natCast_zmod_val ((ZMod.finEquiv (n + 1)) i)).symm
  calc
    norm k M n = ∑ i : Fin (n + 1), cyclicOperator k M n ^ i.val :=
      (Fin.sum_univ_eq_sum_range (fun j => cyclicOperator k M n ^ j) (n + 1)).symm
    _ = ∑ a : Multiplicative (ZMod (n + 1)), cyclicRepresentation k M n a :=
      Fintype.sum_equiv e
        (fun i : Fin (n + 1) => cyclicOperator k M n ^ i.val)
        (cyclicRepresentation k M n) fun i => by rw [he, cyclicRepresentation_natCast]
    _ = (cyclicRepresentation k M n).norm := rfl

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. Define `N_n=∑_(j=0)^n t_n^j`. For `x : T_n`, the norm evaluates as
`N_n(x)=∑_(j=0)^n t_n^j(x)`. -/
theorem norm_apply (n : ℕ) (x : TensorPower k (n + 1) M) :
    norm k M n x = ∑ j ∈ Finset.range (n + 1), (cyclicOperator k M n ^ j) x := by
  change (LinearMap.applyₗ (R := k) x)
      (∑ j ∈ Finset.range (n + 1), cyclicOperator k M n ^ j) = _
  exact map_sum (LinearMap.applyₗ (R := k) x) _ _

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. Define `N_n=∑_(j=0)^n t_n^j`. In degree zero the one-term norm is identity
on the
one-factor tensor power. -/
@[simp]
theorem norm_zero : norm k M 0 = 1 := by
  simp [norm]

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. Define `N_n=∑_(j=0)^n t_n^j`. The cyclic period gives `(1-t_n)N_n=0` as an
endomorphism
of `T_n`. -/
theorem one_sub_cyclicOperator_mul_norm (n : ℕ) :
    (1 - cyclicOperator k M n) * norm k M n = 0 := by
  simpa only [norm, cyclicOperator_period, sub_self] using
    mul_neg_geom_sum (cyclicOperator k M n) (n + 1)

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. Define `N_n=∑_(j=0)^n t_n^j`. The finite geometric sum gives `N_n(1-t_n)=0`
as an
endomorphism of `T_n`. -/
theorem norm_mul_one_sub_cyclicOperator (n : ℕ) :
    norm k M n * (1 - cyclicOperator k M n) = 0 := by
  simpa only [norm, cyclicOperator_period, sub_self] using
    geom_sum_mul_neg (cyclicOperator k M n) (n + 1)

variable {k M} {N : Type w} [AddCommGroup N] [Module k N]

/-- Let `k` be a commutative ring, `f : M →ₗ[k] M′` a linear map of
modules, and `F_n(f)` its map on all `n+1` tensor factors. For the signed operators, `F_n(f) ∘ t_n^M
= t_n^M′ ∘ F_n(f)`. -/
theorem cyclicOperator_natural (f : M →ₗ[k] N) (n : ℕ) :
    (PiTensorProduct.map (fun _ : Fin (n + 1) => f)).comp (cyclicOperator k M n) =
      (cyclicOperator k N n).comp (PiTensorProduct.map (fun _ : Fin (n + 1) => f)) := by
  apply LinearMap.ext
  intro x
  change PiTensorProduct.map (fun _ : Fin (n + 1) => f) (cyclicEquiv k M n x) =
    cyclicEquiv k N n (PiTensorProduct.map (fun _ : Fin (n + 1) => f) x)
  rw [cyclicEquiv_apply, cyclicEquiv_apply, map_smul, rotation_natural]

/-- Let `k` be a commutative ring, `f : M →ₗ[k] M′` a linear map of
modules, and `F_n(f)` its map on all `n+1` tensor factors. For every `j ∈ ℕ`,
`F_n(f)(t_n^j(x))=t_n^j(F_n(f)(x))`. -/
theorem cyclicOperator_pow_natural (f : M →ₗ[k] N) (n j : ℕ)
    (x : TensorPower k (n + 1) M) :
    PiTensorProduct.map (fun _ : Fin (n + 1) => f) ((cyclicOperator k M n ^ j) x) =
      (cyclicOperator k N n ^ j) (PiTensorProduct.map (fun _ : Fin (n + 1) => f) x) := by
  have h := Module.End.commute_pow_left_of_commute (cyclicOperator_natural f n).symm j
  exact (DFunLike.congr_fun h x).symm

/-- Let `k` be a commutative ring, `f : M →ₗ[k] M′` a linear map of
modules, and `F_n(f)` its map on all `n+1` tensor factors. For any element `a ∈ ℤ/(n+1)`, the cyclic
actions satisfy
`F_n(f)(a·x)=a·F_n(f)(x)`. -/
theorem cyclicRepresentation_natural (f : M →ₗ[k] N) (n : ℕ)
    (a : Multiplicative (ZMod (n + 1))) (x : TensorPower k (n + 1) M) :
    PiTensorProduct.map (fun _ : Fin (n + 1) => f) (cyclicRepresentation k M n a x) =
      cyclicRepresentation k N n a (PiTensorProduct.map (fun _ : Fin (n + 1) => f) x) := by
  have ha : Multiplicative.ofAdd (a.toAdd.val : ZMod (n + 1)) = a :=
    congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val a.toAdd)
  rw [← ha, cyclicRepresentation_natCast, cyclicRepresentation_natCast]
  exact cyclicOperator_pow_natural f n a.toAdd.val x

/-- Let `k` be a commutative ring, `f : M →ₗ[k] M′` a linear map of
modules, and `F_n(f)` its map on all `n+1` tensor factors. The full cyclic norms satisfy
`F_n(f)(N_n^M(x))=N_n^M′(F_n(f)(x))`. -/
theorem norm_natural (f : M →ₗ[k] N) (n : ℕ) (x : TensorPower k (n + 1) M) :
    PiTensorProduct.map (fun _ : Fin (n + 1) => f) (norm k M n x) =
      norm k N n (PiTensorProduct.map (fun _ : Fin (n + 1) => f) x) := by
  rw [norm_apply, norm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact cyclicOperator_pow_natural f n j x

variable (k M)

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. For `j ∈ ℕ`, the power on a pure word is
`t_n^j(tprod(a))=(-1)^(nj) • tprod(i ↦ a((finRotate(n+1)^j)⁻¹(i)))`. -/
theorem cyclicOperator_pow_tprod (n j : ℕ) (a : Fin (n + 1) → M) :
    (cyclicOperator k M n ^ j) (PiTensorProduct.tprod k a) =
      (-1 : k) ^ (n * j) • PiTensorProduct.tprod k
        (fun i => a ((finRotate (n + 1) ^ j).symm i)) := by
  induction j with
  | zero =>
      simp
      apply congrArg (PiTensorProduct.tprod k)
      funext i
      rfl
  | succ j ih =>
      have hs : (-1 : k) ^ (n * j) * (-1 : k) ^ n = (-1 : k) ^ (n * (j + 1)) := by
        rw [← pow_add, Nat.mul_succ]
      have he : finRotate (n + 1) ^ (j + 1) =
          (finRotate (n + 1) ^ j).trans (finRotate (n + 1)) := by
        rw [pow_succ', Equiv.Perm.mul_def]
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply, ih,
        map_smul, cyclicOperator_tprod, smul_smul, hs]
      apply congrArg (fun x => (-1 : k) ^ (n * (j + 1)) • PiTensorProduct.tprod k x)
      funext i
      exact (congrArg (fun e : Equiv.Perm (Fin (n + 1)) => a (e.symm i)) he).symm

/-- Let `k` be a commutative ring and `M` a `k`-module.
On `T_n=M^⊗(n+1)`, let `ρ_n` rotate the final factor to the first
and set `t_n=(-1)^nρ_n`. Write `C_(n+1)=ℤ/(n+1)` for the additive cyclic group. For `j ∈ ℕ`, the
inverse residue `[-j]` acts on `tprod(a)`
as `(-1)^(nj) • tprod(i ↦ a(finRotate(n+1)^j(i)))`. -/
theorem cyclicRepresentation_inverse_natCast_tprod (n j : ℕ) (a : Fin (n + 1) → M) :
    cyclicRepresentation k M n
        (Multiplicative.ofAdd ((-(j : ℤ)) : ZMod (n + 1))) (PiTensorProduct.tprod k a) =
      (-1 : k) ^ (n * j) • PiTensorProduct.tprod k
        (fun i => a ((finRotate (n + 1) ^ j) i)) := by
  let T := TensorPower k (n + 1) M
  let E : T ≃ₗ[k] T := cyclicEquiv k M n
  let f : (T ≃ₗ[k] T) →* Module.End k T :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hmap : (E ^ j).toLinearMap = cyclicOperator k M n ^ j := map_pow f E j
  have hp (b : Fin (n + 1) → M) :
      (E ^ j) (PiTensorProduct.tprod k b) =
        (-1 : k) ^ (n * j) • PiTensorProduct.tprod k
          (fun i => b ((finRotate (n + 1) ^ j).symm i)) :=
    (congrArg (fun g : Module.End k T => g (PiTensorProduct.tprod k b)) hmap).trans
      (cyclicOperator_pow_tprod k M n j b)
  have hs : (-1 : k) ^ (n * j) * (-1 : k) ^ (n * j) = 1 := by
    rw [← mul_pow]
    simp
  have hAuto : cyclicAutomorphism k M n
      (Multiplicative.ofAdd (-(j : ZMod (n + 1)))) = E ^ (-(j : ℤ)) := by
    simpa only [Int.cast_neg, Int.cast_natCast] using
      cyclicAutomorphism_intCast k M n (-(j : ℤ))
  change cyclicAutomorphism k M n
      (Multiplicative.ofAdd (-(j : ZMod (n + 1)))) (PiTensorProduct.tprod k a) = _
  rw [hAuto]
  change (E ^ (-(j : ℤ))) (PiTensorProduct.tprod k a) = _
  apply (E ^ j).injective
  have hLeft : (E ^ j) ((E ^ (-(j : ℤ))) (PiTensorProduct.tprod k a)) =
      PiTensorProduct.tprod k a := by
    rw [zpow_neg, zpow_natCast]
    exact (E ^ j).apply_symm_apply _
  have hRight : (E ^ j)
      ((-1 : k) ^ (n * j) • PiTensorProduct.tprod k
        (fun i => a ((finRotate (n + 1) ^ j) i))) = PiTensorProduct.tprod k a := by
    rw [map_smul, hp, smul_smul, hs, one_smul]
    apply congrArg (PiTensorProduct.tprod k)
    funext i
    rw [Equiv.apply_symm_apply]
  exact hLeft.trans hRight.symm

end Signed

section ConsSigned

variable (k : Type u) (M : Type v) [CommRing k] [AddCommGroup M] [Module k M]

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. The transported signed
operator is an endomorphism of
`M ⊗[k] M^⊗n`. -/
def consCyclicOperator (n : ℕ) : Module.End k (M ⊗[k] TensorPower k n M) :=
  (TensorPower.consEquiv k M n).conjRingEquiv.symm (TensorPower.cyclicOperator k M n)

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. The transported action
is a representation of
`ℤ/(n+1)` on `M ⊗[k] M^⊗n`. -/
def consCyclicRepresentation (n : ℕ) :
    Representation k (Multiplicative (ZMod (n + 1))) (M ⊗[k] TensorPower k n M) :=
  (TensorPower.consEquiv k M n).conjRingEquiv.symm.toMonoidHom.comp
    (TensorPower.cyclicRepresentation k M n)

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. The transported finite
sum is the norm endomorphism
on `M ⊗[k] M^⊗n`. -/
def consNorm (n : ℕ) : Module.End k (M ⊗[k] TensorPower k n M) :=
  (TensorPower.consEquiv k M n).conjRingEquiv.symm (TensorPower.norm k M n)

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. For every `x`, the
coordinate comparison satisfies
`c_n(tilde(t)_n(x))=t_n(c_n(x))`. -/
theorem consCyclicOperator_coordinates (n : ℕ) (x : M ⊗[k] TensorPower k n M) :
    consEquiv k M n (consCyclicOperator k M n x) =
      TensorPower.cyclicOperator k M n (consEquiv k M n x) := by
  change TensorPower.consEquiv k M n
    ((TensorPower.consEquiv k M n).symm
      (TensorPower.cyclicOperator k M n (TensorPower.consEquiv k M n x))) = _
  exact (TensorPower.consEquiv k M n).apply_symm_apply _

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. For every cyclic-group
element `a` and tensor `x`,
`c_n(a·x)=a·c_n(x)`. -/
theorem consCyclicRepresentation_coordinates (n : ℕ)
    (a : Multiplicative (ZMod (n + 1))) (x : M ⊗[k] TensorPower k n M) :
    consEquiv k M n (consCyclicRepresentation k M n a x) =
      TensorPower.cyclicRepresentation k M n a (consEquiv k M n x) := by
  change TensorPower.consEquiv k M n
    ((TensorPower.consEquiv k M n).symm
      (TensorPower.cyclicRepresentation k M n a (TensorPower.consEquiv k M n x))) = _
  exact (TensorPower.consEquiv k M n).apply_symm_apply _

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. The norm satisfies
`c_n(tilde(N)_n(x))=N_n(c_n(x))`. -/
theorem consNorm_coordinates (n : ℕ) (x : M ⊗[k] TensorPower k n M) :
    consEquiv k M n (consNorm k M n x) =
      TensorPower.norm k M n (consEquiv k M n x) := by
  change TensorPower.consEquiv k M n
    ((TensorPower.consEquiv k M n).symm
      (TensorPower.norm k M n (TensorPower.consEquiv k M n x))) = _
  exact (TensorPower.consEquiv k M n).apply_symm_apply _

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. For `a : Fin(n+1) → M`,
the operator sends
`a₀ ⊗ tprod(a₁,…,a_n)` to
`(-1)^n • (a_n ⊗ tprod(a₀,…,a_(n-1)))`. -/
@[simp]
theorem consCyclicOperator_tmul (n : ℕ) (a : Fin (n + 1) → M) :
    consCyclicOperator k M n (a 0 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.tail a)) =
      (-1 : k) ^ n •
        (a (Fin.last n) ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin n => a i.castSucc)) := by
  have hrot : (fun i => a ((finRotate (n + 1)).symm i)) =
      Fin.cons (a (Fin.last n)) (fun i : Fin n => a i.castSucc) := by
    funext i
    cases i using Fin.cases with
    | zero =>
      rw [Fin.cons_zero]
      apply congrArg a
      apply (finRotate (n + 1)).symm_apply_eq.mpr
      exact finRotate_last.symm
    | succ i =>
      rw [Fin.cons_succ]
      apply congrArg a
      apply (finRotate (n + 1)).symm_apply_eq.mpr
      exact (finRotate_of_lt i.isLt).symm
  apply (consEquiv k M n).injective
  rw [consCyclicOperator_coordinates, consEquiv_tmul, Fin.cons_self_tail,
    TensorPower.cyclicOperator_tprod, map_smul, consEquiv_tmul, hrot]

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. The transported cyclic
operator satisfies
`tilde(t)_n^(n+1)=id`. -/
theorem consCyclicOperator_period (n : ℕ) : consCyclicOperator k M n ^ (n + 1) = 1 := by
  have h := congrArg (TensorPower.consEquiv k M n).conjRingEquiv.symm
    (TensorPower.cyclicOperator_period k M n)
  simpa only [map_pow, map_one, consCyclicOperator] using h

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. In degree zero the
transported cyclic operator is identity. -/
@[simp]
theorem consCyclicOperator_zero : consCyclicOperator k M 0 = 1 := by
  simp only [consCyclicOperator, TensorPower.cyclicOperator_zero, map_one]

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. For `j ∈ ℕ`, the cyclic
representation at `[j]` equals
`tilde(t)_n^j`. -/
@[simp]
theorem consCyclicRepresentation_natCast (n j : ℕ) :
    consCyclicRepresentation k M n (Multiplicative.ofAdd (j : ZMod (n + 1))) =
      consCyclicOperator k M n ^ j := by
  change (consEquiv k M n).conjRingEquiv.symm
    (cyclicRepresentation k M n (Multiplicative.ofAdd (j : ZMod (n + 1)))) = _
  rw [cyclicRepresentation_natCast, map_pow]
  rfl

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. The residue generator
`[1]` acts by `tilde(t)_n`. -/
@[simp]
theorem consCyclicRepresentation_generator (n : ℕ) :
    consCyclicRepresentation k M n (Multiplicative.ofAdd (1 : ZMod (n + 1))) =
      consCyclicOperator k M n := by
  change (TensorPower.consEquiv k M n).conjRingEquiv.symm
    (TensorPower.cyclicRepresentation k M n (Multiplicative.ofAdd (1 : ZMod (n + 1)))) = _
  rw [TensorPower.cyclicRepresentation_generator]
  rfl

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. The norm is the
geometric sum
`tilde(N)_n=∑_(j=0)^n tilde(t)_n^j`. -/
theorem consNorm_eq_sum (n : ℕ) :
    consNorm k M n = ∑ j ∈ Finset.range (n + 1), consCyclicOperator k M n ^ j := by
  change (TensorPower.consEquiv k M n).conjRingEquiv.symm
    (∑ j ∈ Finset.range (n + 1), TensorPower.cyclicOperator k M n ^ j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact map_pow (TensorPower.consEquiv k M n).conjRingEquiv.symm _ j

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. The geometric sum
equals the finite-group norm of its
transported cyclic representation. -/
theorem consNorm_eq_representation_norm (n : ℕ) :
    consNorm k M n = (consCyclicRepresentation k M n).norm := by
  change (TensorPower.consEquiv k M n).conjRingEquiv.symm (TensorPower.norm k M n) =
    ∑ a : Multiplicative (ZMod (n + 1)),
      (TensorPower.consEquiv k M n).conjRingEquiv.symm (TensorPower.cyclicRepresentation k M n a)
  rw [TensorPower.norm_eq_representation_norm, Representation.norm]
  exact map_sum (TensorPower.consEquiv k M n).conjRingEquiv.symm _ _

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. The degree-zero
transported norm is identity. -/
@[simp]
theorem consNorm_zero : consNorm k M 0 = 1 := by
  simp only [consNorm, TensorPower.norm_zero, map_one]

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. The left telescoping
identity is
`(1-tilde(t)_n)tilde(N)_n=0`. -/
theorem consOne_sub_cyclicOperator_mul_norm (n : ℕ) :
    (1 - consCyclicOperator k M n) * consNorm k M n = 0 := by
  have h := congrArg (TensorPower.consEquiv k M n).conjRingEquiv.symm
    (TensorPower.one_sub_cyclicOperator_mul_norm k M n)
  simpa only [map_mul, map_sub, map_one, map_zero, consCyclicOperator, consNorm] using h

/-- Let `k` be a commutative ring and `M` a `k`-module.
The canonical word identification `c_n : M ⊗[k] M^⊗n ≅ M^⊗(n+1)`
transports the signed rotation `t_n=(-1)^nρ_n`, its cyclic action,
and its norm `N_n=∑_(j=0)^n t_n^j` to the separate-first-factor coordinates. The right telescoping
identity is
`tilde(N)_n(1-tilde(t)_n)=0`. -/
theorem consNorm_mul_one_sub_cyclicOperator (n : ℕ) :
    consNorm k M n * (1 - consCyclicOperator k M n) = 0 := by
  have h := congrArg (TensorPower.consEquiv k M n).conjRingEquiv.symm
    (TensorPower.norm_mul_one_sub_cyclicOperator k M n)
  simpa only [map_mul, map_sub, map_one, map_zero, consCyclicOperator, consNorm] using h

variable {k M} {N : Type w} [AddCommGroup N] [Module k N]

/-- For a commutative ring `k`, modules `M,M′`, and linear
`f : M → M′`, the separate-factor level map is `f` on the
first factor and the tensor-power map of `f` on the `n` tail factors. -/
def consLevelMap (f : M →ₗ[k] N) (n : ℕ) :
    M ⊗[k] TensorPower k n M →ₗ[k] N ⊗[k] TensorPower k n N :=
  TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => f))

/-- For a commutative ring `k` and module `M`, applying its
identity map to the first factor and all `n` tail factors gives
identity on `M ⊗[k] M^⊗n`. -/
@[simp]
theorem consLevelMap_id (n : ℕ) :
    consLevelMap (LinearMap.id : M →ₗ[k] M) n = LinearMap.id := by
  simp only [consLevelMap, PiTensorProduct.map_id, TensorProduct.map_id]

/-- For a commutative ring `k` and linear maps `f : M → M′`,
`g : M′ → P`, the level maps satisfy
`level(g) ∘ level(f)=level(g ∘ f)` in every degree `n`. -/
theorem consLevelMap_comp {P : Type*} [AddCommGroup P] [Module k P]
    (f : M →ₗ[k] N) (g : N →ₗ[k] P) (n : ℕ) :
    (consLevelMap g n).comp (consLevelMap f n) = consLevelMap (g.comp f) n := by
  simp only [consLevelMap, ← TensorProduct.map_comp, ← PiTensorProduct.map_comp]

/-- For a commutative ring `k` and linear `f : M → M′`, the
word identifications intertwine the level map with the map of
`f` on all `n+1` tensor factors. -/
theorem consLevelMap_coordinates (f : M →ₗ[k] N) (n : ℕ)
    (x : M ⊗[k] TensorPower k n M) :
    consEquiv k N n (consLevelMap f n x) =
      PiTensorProduct.map (fun _ : Fin (n + 1) => f) (consEquiv k M n x) := by
  change TensorPower.consEquiv k N n
      (TensorProduct.map f (PiTensorProduct.map (fun _ : Fin n => f)) x) =
    PiTensorProduct.map (fun _ : Fin (n + 1) => f) (TensorPower.consEquiv k M n x)
  exact DFunLike.congr_fun (TensorPower.consEquiv_naturality f n) x

/-- For a commutative ring `k` and linear `f : M → M′`, the
separate-factor level map intertwines the two signed cyclic operators. -/
theorem consCyclicOperator_natural (f : M →ₗ[k] N) (n : ℕ) :
    (consLevelMap f n).comp (consCyclicOperator k M n) =
      (consCyclicOperator k N n).comp (consLevelMap f n) := by
  apply LinearMap.ext
  intro x
  apply (consEquiv k N n).injective
  change consEquiv k N n (consLevelMap f n (consCyclicOperator k M n x)) =
    consEquiv k N n (consCyclicOperator k N n (consLevelMap f n x))
  rw [consLevelMap_coordinates, consCyclicOperator_coordinates, consCyclicOperator_coordinates,
    consLevelMap_coordinates]
  exact DFunLike.congr_fun (TensorPower.cyclicOperator_natural f n)
    (consEquiv k M n x)

/-- For a commutative ring `k`, linear `f : M → M′`, and
`a ∈ ℤ/(n+1)`, the separate-factor level map commutes with
the action of `a`. -/
theorem consCyclicRepresentation_natural (f : M →ₗ[k] N) (n : ℕ)
    (a : Multiplicative (ZMod (n + 1))) (x : M ⊗[k] TensorPower k n M) :
    consLevelMap f n (consCyclicRepresentation k M n a x) =
      consCyclicRepresentation k N n a (consLevelMap f n x) := by
  apply (consEquiv k N n).injective
  rw [consLevelMap_coordinates, consCyclicRepresentation_coordinates,
    consCyclicRepresentation_coordinates, consLevelMap_coordinates]
  exact TensorPower.cyclicRepresentation_natural f n a (consEquiv k M n x)

/-- For a commutative ring `k` and linear `f : M → M′`, the
separate-factor level map commutes with the full cyclic norm. -/
theorem consNorm_natural (f : M →ₗ[k] N) (n : ℕ) (x : M ⊗[k] TensorPower k n M) :
    consLevelMap f n (consNorm k M n x) = consNorm k N n (consLevelMap f n x) := by
  apply (consEquiv k N n).injective
  rw [consLevelMap_coordinates, consNorm_coordinates, consNorm_coordinates,
    consLevelMap_coordinates]
  exact TensorPower.norm_natural f n (consEquiv k M n x)

end ConsSigned

end TensorPower
