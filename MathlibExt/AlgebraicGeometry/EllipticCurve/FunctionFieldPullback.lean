/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_EllipticCurve_FunctionFieldPullback.lean`,
`Definitions/Def_WeierstrassCurve_EDSEngine.lean`,
`Definitions/Def_Compat_Mathlib430.lean`,
`Theorems/Thm_WeierstrassCurve_Affine_eq_zero_of_forall_transEquiv_eq.lean`
and the corresponding `P2M/Sol/S_*.lean` proof files
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.GroupWithZero.Action.Basic
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.Algebra.Ring.AddAut
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Embedding.Set
public import Mathlib.NumberTheory.EllipticDivisibilitySequence
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

import MathlibExt.AlgebraicGeometry.EllipticCurve.TorsionCardinality

@[expose] public noncomputable section

/-!
# Function-field pullbacks on a Weierstrass curve

For a Weierstrass curve `W` over `F` and a field `K` over `F`, this file works in the function
field of `W⁄K`. It defines the generic point `genericPoint W K`, the pullback of functions along
translation by a point (`transEquiv W K S`, an algebra automorphism), the pullback along
multiplication by an integer `n` (`mulPull W K n h`), and the place `placeOf W K P hP` of a nonzero
affine point. `mulPull W K n h` takes a proof `h : MulGood W K n` that `n • genericPoint W K` is
nonzero and is not the base change of a point over `K`; when `K` is algebraically closed, `W` is
elliptic and `(n : K) ≠ 0`, `zsmul_genericPoint_good` provides it.

Valuations at places are those of `IsDedekindDomain.HeightOneSpectrum.valuation`: a value below
`1` means that the function vanishes there, so `WithZero.exp (-1)` is a simple zero and
`WithZero.exp 1` is a simple pole.

## Main results

* `WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq`: let `g` be a function that is fixed
  by translation by every `n`-torsion point and that, at every affine point `P` with `n • P ≠ 0`,
  has a simple zero when `n • P = T` and valuation `1` otherwise. Then `T = 0`.
* `WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq_of_pole`: the same with a simple pole
  in place of the simple zero.
* `WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le`: the function field has degree at most
  `n.natAbs ^ 2` over the image of `mulPull W K n h`.
* `WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed`: over an algebraically closed
  field, every point is divisible by every nonzero integer.

The two nondegeneracy results assume that `(n : K) ≠ 0`, that the coordinate ring of `W⁄K` is a
Dedekind domain, and, as the hypothesis `hpull`, that for every affine point `P` with
`n • P ≠ 0`, the pullback along `mulPull` of a function vanishing to order at least `k` at
`n • P` vanishes to order at least `k` at `P`.
-/


/-
Copyright: the vendored blocks below are verbatim copies from Mathlib (Apache-2.0; see Mathlib's LICENSE),
release v4.30.0 = leanprover-community/mathlib4 commit c5ea00351c28e24afc9f0f84379aa41082b1188f, with declarations
RENAMED (suffix `Finsupp` / trailing prime) so they do not clash with Mathlib v4.33.0. Bodies are the Mathlib v4.30.0 text
with its docstrings omitted, otherwise byte-identical unless a line is marked `-- [port]`.
-/

set_option autoImplicit false

/-! ## Block A — Mathlib v4.30.0 Mathlib/RepresentationTheory/Basic.lean:391-419 (section MulAction), names suffixed `Finsupp` -/

namespace Representation

section MulAction

variable (k : Type*) [Semiring k] (G : Type*) [Monoid G] (H : Type*) [MulAction G H]

noncomputable def ofMulActionFinsupp : Representation k G (H →₀ k) where
  toFun g := Finsupp.lmapDomain k k (g • ·)
  map_one' := by
    ext x y
    simp
  map_mul' x y := by
    ext z w
    simp [mul_smul]

noncomputable abbrev leftRegularFinsupp := ofMulActionFinsupp k G G

noncomputable abbrev diagonalFinsupp (n : ℕ) := ofMulActionFinsupp k G (Fin n → G)

variable {k G H}

theorem ofMulActionFinsupp_def (g : G) : ofMulActionFinsupp k G H g = Finsupp.lmapDomain k k (g • ·) :=
  rfl

@[simp]
theorem ofMulActionFinsupp_single (g : G) (x : H) (r : k) :
    ofMulActionFinsupp k G H g (Finsupp.single x r) = Finsupp.single (g • x) r :=
  Finsupp.mapDomain_single

end MulAction

/-! ## Block B — Mathlib v4.30.0 Mathlib/RepresentationTheory/Basic.lean:472-483 (section Group) -/

section Group

variable {k G V : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)
@[simp]
theorem ofMulActionFinsupp_apply {H : Type*} [MulAction G H] (g : G) (f : H →₀ k) (h : H) :
    ofMulActionFinsupp k G H g f h = f (g⁻¹ • h) := by
  conv_lhs => rw [← smul_inv_smul g h]
  let h' := g⁻¹ • h
  change ofMulActionFinsupp k G H g f (g • h') = f h'
  have hg : Function.Injective (g • · : H → H) := by
    intro h₁ h₂
    simp
  simp only [ofMulActionFinsupp_def, Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_apply_of_injective hg f _

end Group

section Bridge

variable (k : Type*) [Semiring k] (G : Type*) [Monoid G] (H : Type*) [MulAction G H]

noncomputable def ofMulActionFinsuppEquiv : (ofMulActionFinsupp k G H).Equiv (ofMulAction k G H) :=
  Equiv.mk (MonoidAlgebra.coeffLinearEquiv k).symm fun g => by
    rw [ofMulAction_def, ofMulActionFinsupp_def]
    ext
    simp

end Bridge

end Representation

/-! ## Block C — Mathlib v4.30.0 Mathlib/RepresentationTheory/Rep/Basic.lean:336-346 and 404-412, names suffixed `Finsupp` -/

namespace Rep

open CategoryTheory

universe w' u v

variable {k : Type u} {G : Type v} [Ring k] [Monoid G]

section

variable (k G)

noncomputable abbrev ofMulActionFinsupp (H : Type w') [MulAction G H] : Rep k G := -- [port] `noncomputable` added (4.30 file had a noncomputable section)
  of <| Representation.ofMulActionFinsupp k G H

noncomputable abbrev leftRegularFinsupp : Rep k G := -- [port] noncomputable
  ofMulActionFinsupp k G G

noncomputable abbrev diagonalFinsupp (n : ℕ) : Rep k G := -- [port] noncomputable
  ofMulActionFinsupp k G (Fin n → G)

noncomputable def ofMulActionFinsuppIso (H : Type w') [MulAction G H] :
    ofMulActionFinsupp k G H ≅ ofMulAction k G H :=
  mkIso (Representation.ofMulActionFinsuppEquiv k G H)

end

noncomputable abbrev leftRegularHomFinsupp (A : Rep k G) (x : A) : leftRegularFinsupp k G ⟶ A := -- [port] noncomputable
  Rep.ofHom ⟨Finsupp.lift A k G fun g ↦ A.ρ g x, fun g ↦ by ext; simp⟩

theorem leftRegularHomFinsupp_hom_single {A : Rep k G} (g : G) (x : A) (r : k) :
    (leftRegularHomFinsupp A x).hom (.single g r) = r • A.ρ g x := by
  simp [leftRegularHomFinsupp]

end Rep

/-! ## Block D — AddAut: Mathlib v4.30.0 Mathlib/Algebra/Group/End.lean:746-801 (+ GroupWithZero/Action/Basic.lean:89-92 and :104-112, Ring/AddAut.lean:32), lemma names primed -/

namespace AddAut

section Compat430

variable (A : Type*) [Add A]

instance : Group (AddAut A) where
  mul g h := AddEquiv.trans h g
  one := AddEquiv.refl _
  inv := AddEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel := AddEquiv.self_trans_symm

/- The following thirteen lemmas are Mathlib v4.30.0 `Mathlib/Algebra/Group/End.lean:758-801`
verbatim except that each name carries a trailing prime. -/

@[simp]
theorem coe_mul' (e₁ e₂ : AddAut A) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl

@[simp]
theorem coe_one' : ⇑(1 : AddAut A) = id :=
  rfl

@[simp]
theorem coe_inv' (e : AddAut A) : ⇑e⁻¹ = e.symm := rfl

theorem mul_def' (e₁ e₂ : AddAut A) : e₁ * e₂ = e₂.trans e₁ :=
  rfl

theorem one_def' : (1 : AddAut A) = AddEquiv.refl _ :=
  rfl

theorem inv_def' (e₁ : AddAut A) : e₁⁻¹ = e₁.symm :=
  rfl

@[simp]
theorem mul_apply' (e₁ e₂ : AddAut A) (a : A) : (e₁ * e₂) a = e₁ (e₂ a) :=
  rfl

@[simp]
theorem one_apply' (a : A) : (1 : AddAut A) a = a :=
  rfl

@[simp]
theorem inv_symm' (e : AddAut A) : e⁻¹.symm = e := rfl

@[simp]
theorem symm_inv' (e : AddAut A) : e.symm⁻¹ = e := rfl

@[simp]
theorem inv_apply' (e : AddAut A) (a : A) : e⁻¹ a = e.symm a := rfl

theorem inv_apply_self' (e : AddAut A) (a : A) : e⁻¹ (e a) = a :=
  AddEquiv.apply_symm_apply _ _

theorem apply_inv_self' (e : AddAut A) (a : A) : e (e⁻¹ a) = a :=
  AddEquiv.apply_symm_apply _ _

example (e₁ e₂ : AddAut A) : e₁ * e₂ = e₁ + e₂ := rfl
example : (1 : AddAut A) = 0 := rfl
example (e : AddAut A) : e⁻¹ = -e := rfl

end Compat430

end AddAut

@[simps]
def DistribMulAction.toAddAut' (G A : Type*) [Group G] [AddMonoid A] [DistribMulAction G A] :
    G →* AddAut A where
  toFun := DistribMulAction.toAddEquiv A
  map_one' := AddEquiv.ext (one_smul _)
  map_mul' _ _ := AddEquiv.ext (mul_smul _ _)

@[simps! +simpRhs]
def AddAut.mulLeft' {R : Type*} [Semiring R] : Rˣ →* AddAut R :=
  DistribMulAction.toAddAut' _ _

/-! ### Block D (continued) — Mathlib v4.30.0 Mathlib/Algebra/GroupWithZero/Action/Basic.lean:104-112: the tautological `DistribMulAction (AddAut A) A`
(`AddAut.applyDistribMulAction`, its `smul_def` and `apply_faithfulSMul`), dropped in v4.33.0 together with the multiplicative structure;
vendored with primed names on top of the Group instance above. -/

namespace AddAut
instance applyDistribMulAction' {A : Type*} [AddMonoid A] : DistribMulAction (AddAut A) A where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero := AddEquiv.map_zero
  smul_add := AddEquiv.map_add

@[simp] protected theorem smul_def' {A : Type*} [AddMonoid A] (f : AddAut A) (a : A) : f • a = f a := rfl

instance apply_faithfulSMul' {A : Type*} [AddMonoid A] : FaithfulSMul (AddAut A) A :=
  ⟨fun h => AddEquiv.ext h⟩
end AddAut

/-! ## Block E — elliptic (divisibility) sequence predicates: Mathlib v4.30.0
Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:78-110 (verbatim; names primed). Vendored because Mathlib v4.33.0 (db584cd6,
same file :286-295) RENAMED AND REDEFINED them (`IsEllipticSequence W := ∀ p q r, IsEllipticNet.rel W p q r 0 = 0`,
`IsDvdSequence` over ℤ instead of ℕ) and kept the 4.30 names only as deprecated aliases of the NEW predicates. -/

section IsEllDivSequence430

universe u

variable {R : Type u} [CommRing R]

variable (W : ℤ → R)

def IsEllSequence' : Prop :=
  ∀ m n r : ℤ, W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2

def IsDivSequence' : Prop :=
  ∀ m n : ℕ, m ∣ n → W m ∣ W n

def IsEllDivSequence' : Prop :=
  IsEllSequence' W ∧ IsDivSequence' W

lemma isEllSequence'_id : IsEllSequence' id :=
  fun _ _ _ => by simp_rw [id_eq]; ring1

lemma isDivSequence'_id : IsDivSequence' id :=
  fun _ _ => Int.ofNat_dvd.mpr

theorem isEllDivSequence'_id : IsEllDivSequence' id :=
  ⟨isEllSequence'_id, isDivSequence'_id⟩

variable {W}

lemma IsEllSequence'.smul (h : IsEllSequence' W) (x : R) : IsEllSequence' (x • W) :=
  fun m n r => by
    linear_combination (norm := (simp_rw [Pi.smul_apply, smul_eq_mul]; ring1)) x ^ 4 * h m n r

lemma IsDivSequence'.smul (h : IsDivSequence' W) (x : R) : IsDivSequence' (x • W) :=
  fun m n r => mul_dvd_mul_left x <| h m n r

lemma IsEllDivSequence'.smul (h : IsEllDivSequence' W) (x : R) : IsEllDivSequence' (x • W) :=
  ⟨h.left.smul x, h.right.smul x⟩

end IsEllDivSequence430


/-! ## Block F — notation `α ^+ M` for `FixedPoints.addSubgroup M α`: Mathlib v4.30.0 Mathlib/Algebra/Ring/Action/Submonoid.lean:43
(verbatim). Mathlib v4.33.0 removed the notation line; the definition itself is unchanged, so re-declaring the notation keeps
every tree statement that uses it textually and semantically identical. -/

notation α "^+" M:51 => FixedPoints.addSubgroup M α

/-! ## Block G — ramification/inertia cardinality lemmas under the separability hypothesis (adapted from Mathlib v4.30.0,
Mathlib/NumberTheory/RamificationInertia/Galois.lean; v4.33.0 restates them assuming PerfectField of the residue field). Theorems only,
primed names; no definitions involved. -/

namespace Ideal

section inertia430

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

open scoped Pointwise


attribute [local instance] Ideal.Quotient.field in
theorem card_stabilizer_eq_card_inertia_mul_finrank' (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (MulAction.stabilizer G P) = Nat.card (inertia G P) *
      Module.finrank (R ⧸ p) (S ⧸ P) := by
  have : IsGalois (R ⧸ p) (S ⧸ P) := { __ := Ideal.Quotient.normal (A := R) G p P }
  have := Ideal.Quotient.finite_of_isInvariant G p P
  have : Subgroup.index _ = _ := Nat.card_congr
    (Quotient.stabilizerQuotientInertiaEquiv G p P).toEquiv
  rw [← IsGalois.card_aut_eq_finrank, ← this,
    ← ((inertia G P).subgroupOf (MulAction.stabilizer G P)).card_mul_index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inertia_le_stabilizer (M := G) P)).toEquiv,
    AddSubgroup.subgroupOf_inertia]

lemma ncard_primesOver_mul_card_inertia_mul_finrank' (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    (p.primesOver S).ncard * Nat.card (P.inertia G) *
      Module.finrank (R ⧸ p) (S ⧸ P) = Nat.card G := by
  rw [mul_assoc, ← card_stabilizer_eq_card_inertia_mul_finrank',
    ← Algebra.IsInvariant.orbit_eq_primesOver R S G p P]
  simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)

attribute [local instance] Ideal.Quotient.field in
lemma card_inertia_eq_ramificationIdxIn'
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
    [Module.IsTorsionFree R S]
    (p : Ideal R) (hp : p ≠ ⊥)
    (P : Ideal S) [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (P.inertia G) = Ideal.ramificationIdxIn p S := by
  have := (show p.IsPrime from P.over_def p ▸ inferInstance).isMaximal hp
  have H := ncard_primesOver_mul_card_inertia_mul_finrank' (G := G) p P
  refine mul_right_injective₀ (IsDedekindDomain.primesOver_ncard_ne_zero p S) ?_
  refine mul_left_injective₀ (b := Module.finrank (R ⧸ p) (S ⧸ P)) ?_ ?_
  · intro e; simp [e, eq_comm, Nat.card_eq_zero, ‹Finite G›.not_infinite] at H
  dsimp only
  rw [H, mul_assoc, ← inertiaDeg_eq_of_isMaximal p P, ← inertiaDegIn_eq_inertiaDeg p P G,
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G]

attribute [local instance] Ideal.Quotient.field in
lemma card_stabilizer_eq' [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
    [Module.IsTorsionFree R S] (p : Ideal R) (hp : p ≠ ⊥) (P : Ideal S) [P.LiesOver p] [P.IsMaximal]
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Nat.card (MulAction.stabilizer G P) = p.ramificationIdxIn S * p.inertiaDegIn S := by
  have := (show p.IsPrime from P.over_def p ▸ inferInstance).isMaximal hp
  rw [card_stabilizer_eq_card_inertia_mul_finrank' p P, card_inertia_eq_ramificationIdxIn' p hp,
    inertiaDegIn_eq_inertiaDeg p P G, inertiaDeg_eq_of_isMaximal p P]

end inertia430

end Ideal

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve

instance instIsEllipticBaseChange {R : Type*} {A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (W : WeierstrassCurve R) [W.IsElliptic] : (W.baseChange A).IsElliptic :=
  inferInstanceAs <| (W.map (algebraMap R A)).IsElliptic

end WeierstrassCurve


section PortEllSequenceCore

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : ℤ → R)
variable {F} [FunLike F R S] [RingHomClass F R S] (f : F)

open scoped nonZeroDivisors

namespace EllSequence

def addMulSub (m n : ℤ) : R := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)

def rel₄ (a b c d : ℤ) : R :=
  addMulSub W a b * addMulSub W c d
    - addMulSub W a c * addMulSub W b d + addMulSub W a d * addMulSub W b c

def net (p q r s : ℤ) : R :=
  W (p + q + s) * W (p - q) * W (r + s) * W r
    - W (p + r + s) * W (p - r) * W (q + s) * W q
    + W (q + r + s) * W (q - r) * W (p + s) * W p

variable {W} in
lemma net_eq_rel₄ {p q r s : ℤ} :
    net W p q r s = rel₄ W (2 * p + s) (2 * q + s) (2 * r + s) s := by
  simp_rw [net, rel₄, addMulSub, add_add_add_comm _ s, add_sub_add_comm, sub_self, add_zero,
    add_assoc, ← two_mul, add_sub_cancel_right, ← left_distrib, ← mul_sub_left_distrib,
    Int.mul_tdiv_cancel_left _ two_ne_zero]
  ring

def Rel₃ (m n r : ℤ) : Prop :=
  W (m + n) * W (m - n) * W r ^ 2 =
    W (m + r) * W (m - r) * W n ^ 2 - W (n + r) * W (n - r) * W m ^ 2

lemma _root_.isEllSequence_iff_rel₃ : IsEllSequence' W ↔ ∀ m n r : ℤ, Rel₃ W m n r :=
  Iff.rfl

def invarNum (s n : ℤ) : R :=
  (W (n + 2 * s) * W (n - s) ^ 2 + W (n + s) ^ 2 * W (n - 2 * s)) * W s ^ 2
    + W n ^ 3 * W (2 * s) ^ 2

def invarDenom (s n : ℤ) : R := W (n + s) * W n * W (n - s)

theorem invar_of_net (net_eq_zero : ∀ p q r s, net W p q r s = 0) (s m n : ℤ) :
    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m := by
  simp_rw [invarNum, invarDenom]
  linear_combination (norm := (simp_rw [net]; ring_nf))
    net_eq_zero m n s 0 * W m * W n * W (2 * s) ^ 2
      - (net_eq_zero m n s s * W (m - s) * W (n - s)
        + net_eq_zero (m - s) (n - s) s s * W (m + s) * W (n + s)
        - net_eq_zero (n + s) n (n - s) (m - n) * W (m - n) * W (2 * s)) * W s ^ 2

lemma net_add_sub_iff (m n : ℤ) :
    net W (m + n) m (m - n) n = 0 ↔
      W (2 * (m + n)) * W (m - n) * W m * W n =
        (W (2 * m + n) * W (2 * n) * W m - W (m + 2 * n) * W (2 * m) * W n) * W (m + n) := by
  rw [net]; conv_rhs => rw [← sub_eq_zero]
  ring_nf

lemma addMulSub_two_zero : addMulSub W 2 0 = W 1 ^ 2 := (sq _).symm
lemma addMulSub_three_one : addMulSub W 3 1 = W 2 * W 1 := rfl

lemma addMulSub_even (m n : ℤ) : addMulSub W (2 * m) (2 * n) = W (m + n) * W (m - n) := by
  simp_rw [addMulSub, ← left_distrib, ← mul_sub_left_distrib,
    Int.mul_tdiv_cancel_left _ two_ne_zero]

lemma addMulSub_odd (m n : ℤ) :
    addMulSub W (2 * m + 1) (2 * n + 1) = W (m + n + 1) * W (m - n) := by
  have h k := Int.mul_tdiv_cancel_left k two_ne_zero
  rw [addMulSub, ← h (m + n + 1), ← h (m - n)]; congr <;> ring

lemma addMulSub_same (zero : W 0 = 0) (m : ℤ) : addMulSub W m m = 0 := by
  rw [addMulSub, sub_self, Int.zero_tdiv, zero, mul_zero]

lemma addMulSub_neg₀ (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W (-m) n = addMulSub W m n := by
  simp_rw [addMulSub, ← neg_add', neg_add_eq_sub, ← neg_sub m, Int.neg_tdiv, neg]; ring

lemma addMulSub_neg₁ (m n : ℤ) : addMulSub W m (-n) = addMulSub W m n := by
  rw [addMulSub, addMulSub, mul_comm]; abel_nf

lemma addMulSub_abs₀ (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W |m| n = addMulSub W m n := by
  obtain h | h := abs_choice m <;> simp only [h, addMulSub_neg₀ W neg]

lemma addMulSub_abs₁ (m n : ℤ) : addMulSub W m |n| = addMulSub W m n := by
  obtain h | h := abs_choice n <;> simp only [h, addMulSub_neg₁]

lemma addMulSub_swap (neg : ∀ k, W (-k) = -W k) (m n : ℤ) :
    addMulSub W m n = - addMulSub W n m := by
  rw [addMulSub, addMulSub, ← neg_sub, Int.neg_tdiv, neg]; ring_nf

section transf

variable (a b c d : ℤ)

def StrictAnti₄ : Prop := 0 ≤ d ∧ d < c ∧ c < b ∧ b < a

def HaveSameParity₄ : Prop :=
  a.negOnePow = b.negOnePow ∧ b.negOnePow = c.negOnePow ∧ c.negOnePow = d.negOnePow

def avg₄ : ℤ := (a + b + c + d) / 2

namespace HaveSameParity₄
open Int Equiv

variable {W a b c d} (same : HaveSameParity₄ a b c d)

include same in
lemma rel₄_eq_net : rel₄ W a b c d = net W ((a - d) / 2) ((b - d) / 2) ((c - d) / 2) d := by
  have h := @Int.two_mul_ediv_two_of_even
  rw [net_eq_rel₄, h, h, h]; · simp_rw [sub_add_cancel]
  all_goals simp only [← negOnePow_eq_iff, same.1, same.2.1, same.2.2]

include same in
lemma even_sum : Even (a + b + c + d) := by
  simp_rw [← negOnePow_eq_one_iff, negOnePow_add,
    same.1, same.2.1, same.2.2, units_mul_self, one_mul, units_mul_self]

include same in
lemma avg₄_add_avg₄ : avg₄ a b c d + avg₄ a b c d = a + b + c + d := by
  rw [← two_mul]; exact Int.mul_ediv_cancel' same.even_sum.two_dvd

include same in
lemma same₀₃ : a.negOnePow = d.negOnePow := by rw [same.1, same.2.1, same.2.2]

include same in
protected lemma abs : HaveSameParity₄ |a| |b| |c| |d| := by
  simpa only [HaveSameParity₄, negOnePow_abs] using same

lemma perm (σ : Perm (Fin 4)) :
    ∀ t : Fin 4 → ℤ, HaveSameParity₄ (t 0) (t 1) (t 2) (t 3) →
      HaveSameParity₄ (t (σ 0)) (t (σ 1)) (t (σ 2)) (t (σ 3)) := by
  have := (Perm.mclosure_swap_castSucc_succ 3).symm ▸ Submonoid.mem_top σ
  refine Submonoid.closure_induction ?_ (fun _ ↦ id) (fun σ τ _ _ hσ hτ t same ↦ ?_) this
  on_goal 2 => simp_rw [Perm.mul_apply]; exact hτ (t ∘ σ) (hσ _ same)
  rintro _ ⟨i, rfl⟩ t ⟨h₀₁, h₁₂, h₂₃⟩; fin_cases i
  exacts [⟨h₀₁.symm, h₀₁ ▸ h₁₂, h₂₃⟩, ⟨h₀₁ ▸ h₁₂, h₁₂.symm, h₁₂ ▸ h₂₃⟩, ⟨h₀₁, h₁₂ ▸ h₂₃, h₂₃.symm⟩]
include same in
lemma six_le_of_strictAnti₄ (anti : StrictAnti₄ a b c d) : 6 ≤ a := by
  simp_rw [HaveSameParity₄, negOnePow_eq_iff] at same
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  rw [← add_two_le_iff_lt_of_even_sub] at hdc hcb hba
  · linarith
  exacts [same.1, same.2.1, same.2.2]

variable (W) in

def addMulSub₄ (a b c d : ℤ) : R := W ((a + b).tdiv 2) * W ((c - d).tdiv 2)

lemma addMulSub₄_mul_addMulSub₄ :
    addMulSub₄ W a b c d * addMulSub₄ W c d a b = addMulSub W a b * addMulSub W c d := by
  simp_rw [addMulSub₄, addMulSub]; ring

include same in
lemma addMulSub_transf :
    addMulSub W (avg₄ a b c d - d) (avg₄ a b c d - c) = addMulSub₄ W a b c d ∧
      addMulSub W (avg₄ a b c d - d) (avg₄ a b c d - b) = addMulSub₄ W a c b d ∧
      addMulSub W (avg₄ a b c d - d) |avg₄ a b c d - a| = addMulSub₄ W b c a d ∧
      addMulSub W (avg₄ a b c d - c) (avg₄ a b c d - b) = addMulSub₄ W a d b c ∧
      addMulSub W (avg₄ a b c d - c) |avg₄ a b c d - a| = addMulSub₄ W b d a c ∧
      addMulSub W (avg₄ a b c d - b) |avg₄ a b c d - a| = addMulSub₄ W c d a b := by
  simp_rw [addMulSub_abs₁, addMulSub, addMulSub₄, sub_add_sub_comm, same.avg₄_add_avg₄]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring_nf

include same in
theorem rel₄_transf :
    rel₄ W (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| =
      rel₄ W a b c d := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := same.addMulSub_transf (W := W)
  simp_rw [rel₄, h₁, h₂, h₃, h₄, h₅, h₆, addMulSub₄_mul_addMulSub₄, mul_comm]

include same in
theorem transf : HaveSameParity₄
    (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| := by
  simp_rw [HaveSameParity₄, negOnePow_abs, negOnePow_sub, same.1, same.2.1, same.2.2, true_and]

include same in
theorem strictAnti₄_transf (anti : StrictAnti₄ a b c d) :
    StrictAnti₄ (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| := by
  obtain ⟨hd, hdc, hcb, hba⟩ := anti
  refine ⟨abs_nonneg _, abs_lt.mpr ⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [← sub_pos]
  · rw [sub_neg_eq_add, sub_add_sub_comm, same.avg₄_add_avg₄]; linarith only [hd, hdc]
  all_goals linarith only [hdc, hcb, hba]

end HaveSameParity₄

end transf

def rel₆ (k l a b c d : ℤ) : R := addMulSub W k l * rel₄ W a b c d

lemma rel₃_iff₄ (m n r : ℤ) :
    Rel₃ W m n r ↔ rel₄ W (2 * m) (2 * n) (2 * r) 0 = 0 := by
  rw [rel₄, ← mul_zero 2, Rel₃]
  simp_rw [addMulSub_even, add_zero, sub_zero]
  convert sub_eq_zero.symm using 2; ring

lemma rel₆_eq₃ (c d m n r : ℤ) :
    rel₆ W c d m n r c = rel₆ W m c n r c d - rel₆ W n c m r c d + rel₆ W r c m n c d := by
  simp_rw [rel₆, rel₄]; ring

lemma rel₆_eq₃' (c d m n r : ℤ) :
    rel₆ W c d m n r d = rel₆ W m d n r c d - rel₆ W n d m r c d + rel₆ W r d m n c d := by
  simp_rw [rel₆, rel₄]; ring

theorem rel₆_eq₁₀ (c d m n r s : ℤ) :
    rel₆ W c d m n r s =
      rel₆ W n d m r s c - rel₆ W r d m n s c + rel₆ W s d m n r c
      + rel₆ W n c m r s d - rel₆ W r c m n s d + rel₆ W s c m n r d
      + rel₆ W n r m s c d - rel₆ W n s m r c d + rel₆ W r s m n c d
      - 2 * rel₆ W m d n r s c := by
  simp_rw [rel₆, rel₄]; ring

theorem addMulSub_sq_mul_rel₄_eq₉ (c d m n r s : ℤ) :
    (addMulSub W c d) ^ 2 * rel₄ W m n r s =
      addMulSub W m c * (rel₆ W n d r s c d - rel₆ W r d n s c d + rel₆ W s d n r c d)

      - addMulSub W m d * (rel₆ W n c r s c d - rel₆ W r c n s c d + rel₆ W s c n r c d)
      + addMulSub W c d * (rel₆ W n r m s c d - rel₆ W n s m r c d + rel₆ W r s m n c d) := by

  simp_rw [rel₆, rel₄]; ring

def OddRec (m : ℤ) : Prop :=
  W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3

def EvenRec (m : ℤ) : Prop :=
  W (2 * m) * W 2 * W 1 ^ 2 = W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2)

lemma rel₃_iff_oddRec (m : ℤ) : Rel₃ W (m + 1) m 1 ↔ OddRec W m := by
  rw [Rel₃, OddRec]; ring_nf

lemma rel₃_iff_evenRec (m : ℤ) : Rel₃ W (m + 1) (m - 1) 1 ↔ EvenRec W m := by
  rw [Rel₃, EvenRec]; ring_nf

lemma rel₄_iff_evenRec (m : ℤ) : rel₄ W (2 * m + 1) (2 * m - 1) 3 1 = 0 ↔ EvenRec W m := by
  rw [iff_comm, EvenRec, ← sub_eq_zero, show 2 * m - 1 = 2 * (m - 1) + 1 by ring]
  change _ ↔ rel₄ W (2 * m + 1) (2 * (m - 1) + 1) (2 * 1 + 1) (2 * 0 + 1) = 0
  simp_rw [rel₄, addMulSub_odd]; ring_nf

def dMin (a : ℤ) : ℤ := if Even a then 0 else 1

def cMin (a : ℤ) : ℤ := dMin a + 2

lemma dMin_nonneg (a : ℤ) : 0 ≤ dMin a := by rw [dMin]; split_ifs <;> decide

lemma dMin_lt_cMin (a : ℤ) : dMin a < cMin a := lt_add_of_pos_right _ zero_lt_two

lemma negOnePow_cMin_eq_dMin (a : ℤ) : (cMin a).negOnePow = (dMin a).negOnePow := by
  rw [cMin, Int.negOnePow_add]; exact mul_one _

lemma negOnePow_dMin (a : ℤ) : (dMin a).negOnePow = a.negOnePow := by
  rw [dMin]; split_ifs with h
  · simp [Int.negOnePow_even a h]
  · simp [Int.negOnePow_odd a (Int.not_even_iff_odd.mp h)]
lemma negOnePow_cMin (a : ℤ) : (cMin a).negOnePow = a.negOnePow := by
  rw [negOnePow_cMin_eq_dMin, negOnePow_dMin]

variable {W}
lemma addMulSub_mem_nonZeroDivisors (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (a : ℤ) :
    addMulSub W (cMin a) (dMin a) ∈ R⁰ := by
  rw [cMin, dMin]; split_ifs; exacts [mul_mem one one, mul_mem two one]

lemma dMin_le {a b : ℤ} (same : a.negOnePow = b.negOnePow) (h : 0 ≤ b) : dMin a ≤ b := by
  rw [dMin]; split_ifs with odd
  exacts [h, h.lt_of_ne (by rintro rfl; exact odd (a.negOnePow_eq_one_iff.mp same))]

open Int

section Rel₄OfValid

variable (W) in

def Rel₄OfValid (a b c d : ℤ) : Prop :=
  HaveSameParity₄ a b c d → StrictAnti₄ a b c d → rel₄ W a b c d = 0

variable {a c₀ d₀ : ℤ} (par : c₀.negOnePow = d₀.negOnePow) (le : 0 ≤ d₀) (lt : d₀ < c₀)
  (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b c₀ d₀) (mem : addMulSub W c₀ d₀ ∈ R⁰)

include par le lt rel mem in

lemma rel₄_fix₁_of_fix₂ (b c : ℤ) :
    Rel₄OfValid W a b c c₀ ∧ (c₀ < c → Rel₄OfValid W a b c d₀) := by
  refine ⟨fun same anti ↦ (mem_nonZeroDivisors_iff.mp mem).2 _ ?_,
    fun _hc same anti ↦ (mem_nonZeroDivisors_iff.mp mem).2 _ ?_⟩ <;> rw [mul_comm, ← rel₆]
  on_goal 1 => rw [rel₆_eq₃]; have _hc := trivial
  on_goal 2 => rw [rel₆_eq₃']
  all_goals simp_rw [rel₆]; rw [rel le_rfl, rel le_rfl, rel anti.2.2.2.le]
  iterate 2
    simp_rw [mul_zero, add_zero, sub_zero]
    iterate 3
      simp only [HaveSameParity₄, par, same.1, same.2.1, same.2.2, true_and]
      refine ⟨le, lt, ?_, ?_⟩ <;> linarith only [_hc, anti.2.1, anti.2.2.1, anti.2.2.2]
include par le lt rel mem in

lemma rel₄_of_fix₂ (b c d : ℤ) (hc : c₀ < d) (par' : d.negOnePow = d₀.negOnePow) :
    Rel₄OfValid W a b c d := fun same ⟨_, hdc, hcb, hba⟩ ↦
      (mem_nonZeroDivisors_iff.mp mem).2 _ <| by
  rw [mul_comm, ← rel₆, rel₆_eq₁₀]; simp_rw [rel₆]
  have fix₁ b c := (rel₄_fix₁_of_fix₂ par le lt rel mem b c).1
  have fix₂ {b c} := (rel₄_fix₁_of_fix₂ par le lt rel mem b c).2
  rw [fix₁, fix₁, fix₁, fix₂ hc, fix₂ hc, fix₂ (hc.trans hdc), rel le_rfl, rel le_rfl,
    rel le_rfl, (rel₄_fix₁_of_fix₂ par le lt (fun h ↦ rel <| h.trans hba.le) mem _ _).1]
  · simp_rw [mul_zero, add_zero, sub_zero]
  iterate 10
    simp only [HaveSameParity₄, par, par', same.1, same.2.1, same.2.2, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [hc, le, lt, hdc, hcb, hba]

theorem rel₄_of_min₂ (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b (cMin a) (dMin a)) (b c d : ℤ) :
    Rel₄OfValid W a b c d := fun same anti ↦ by
  obtain hc|hc := lt_or_ge (cMin a) d
  · refine rel₄_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel
      (addMulSub_mem_nonZeroDivisors one two a) _ _ _ hc ?_ same anti
    rw [negOnePow_dMin, same.1, same.2.1, same.2.2]
  have fix := rel₄_fix₁_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel
    (addMulSub_mem_nonZeroDivisors one two a) b c
  obtain rfl|hc := (show d ≤ cMin a from hc).eq_or_lt
  · exact fix.1 same anti
  obtain rfl : dMin a = d := (dMin_le same.same₀₃ anti.1).antisymm <| by
    rwa [← add_two_le_iff_lt_of_even_sub, cMin, add_le_add_iff_right] at hc
    rw [← negOnePow_eq_iff, negOnePow_cMin, same.same₀₃]
  obtain rfl|hc : cMin a = c ∨ _ := ((add_two_le_iff_lt_of_even_sub <| by
    rw [← negOnePow_eq_iff, negOnePow_dMin, same.1, same.2.1]).mpr anti.2.1).eq_or_lt
  exacts [rel le_rfl same anti, fix.2 hc same anti]
theorem rel₄_of_anti_oddRec_evenRec (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m) :
    ∀ ⦃a b c d : ℤ⦄, Rel₄OfValid W a b c d :=
  Int.strongRec (m := 6)
    (fun a ha b c d same anti ↦
      absurd (ha.trans_le (same.six_le_of_strictAnti₄ anti)) (lt_irrefl a))
    fun a h6 ih ↦ rel₄_of_min₂ one two fun {a' b} haa same anti ↦ by
  obtain ha'|ha' := haa.lt_or_eq
  · exact ih _ ha' same anti
  obtain hba|rfl := lt_or_eq_of_le <| show b + 2 ≤ a' from
    (add_two_le_iff_lt_of_even_sub <| (negOnePow_eq_iff _ _).1 same.1).mpr anti.2.2.2
  · rw [← same.rel₄_transf]
    refine ih _ ?_ same.transf (same.strictAnti₄_transf anti)
    rw [avg₄, sub_lt_iff_lt_add, Int.ediv_lt_iff_lt_mul zero_lt_two, ← ha', cMin]
    linarith only [hba]
  obtain ⟨m, rfl|rfl⟩ := b.even_or_odd'
  · have ea : Even a := by rw [← ha']; exact (even_two_mul _).add even_two
    simp_rw [cMin, dMin, if_pos ea]
    have hm : m ≥ 2 := by linarith only [h6, ha']
    convert (rel₃_iff₄ W (m + 1) m 1).mp ((rel₃_iff_oddRec W m).mpr <| oddRec _ hm) using 2
    all_goals ring
  · have nea : ¬ Even a := by
      rw [← ha', Int.not_even_iff_odd]; convert odd_two_mul_add_one (m + 1) using 1; ring
    simp_rw [cMin, dMin, if_neg nea]
    have hm : m + 1 ≥ 3 := by linarith only [h6, ha']
    convert (rel₄_iff_evenRec W (m + 1)).mpr (evenRec _ hm) using 2
    all_goals ring
end Rel₄OfValid

section Perm

variable (neg : ∀ k, W (-k) = -W k)

include neg in
lemma rel₄_abs {m n r s : ℤ} : rel₄ W |m| |n| |r| |s| = rel₄ W m n r s := by
  simp_rw [rel₄, addMulSub_abs₀ W neg, addMulSub_abs₁]

include neg in
lemma rel₄_swap₀₁ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W n m r s := by
  simp_rw [rel₄, addMulSub_swap W neg n m]; ring

include neg in
lemma rel₄_swap₁₂ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W m r n s := by
  simp_rw [rel₄, addMulSub_swap W neg r n]; ring

include neg in
lemma rel₄_swap₂₃ {m n r s : ℤ} : rel₄ W m n r s = - rel₄ W m n s r := by
  simp_rw [rel₄, addMulSub_swap W neg s r]; ring

open Equiv

variable (W) in

def relFin4 (t : Fin 4 → ℤ) : R := rel₄ W (t 0) (t 1) (t 2) (t 3)

include neg in

theorem relFin4_perm (σ : Perm (Fin 4)) : ∀ t, relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t := by
  have := (Perm.mclosure_swap_castSucc_succ 3).symm ▸ Submonoid.mem_top σ
  refine Submonoid.closure_induction ?_ (by simp) (fun σ τ _ _ hσ hτ t ↦ ?_) this
  · rintro _ ⟨i, rfl⟩ t; fin_cases i <;>
      rw [Perm.sign_swap (Fin.castSucc_lt_succ).ne, Units.neg_smul, one_smul]
    exacts [rel₄_swap₀₁ neg, rel₄_swap₁₂ neg, rel₄_swap₂₃ neg]
  rw [Perm.coe_mul, ← Function.comp_assoc, hτ, hσ, map_mul, mul_comm, mul_smul]
include neg in
lemma relFin4_perm' (σ : Perm (Fin 4)) (t) : Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t := by
  rw [relFin4_perm neg, ← mul_smul, Int.units_mul_self, one_smul]
variable (zero : W 0 = 0)

include zero in
lemma rel₄_same₀₁ (m r s : ℤ) : rel₄ W m m r s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

include zero in
lemma rel₄_same₁₂ (m n s : ℤ) : rel₄ W m n n s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

include zero in
lemma rel₄_same₂₃ (m n r : ℤ) : rel₄ W m n r r = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
  (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m)

include neg zero one two oddRec evenRec in

theorem rel₄_of_oddRec_evenRec {a b c d : ℤ} (same : HaveSameParity₄ a b c d) :
    rel₄ W a b c d = 0 := by
  let t := ![|a|, |b|, |c|, |d|]
  have nonneg i : 0 ≤ t i := by fin_cases i <;> exact abs_nonneg _
  let σ := Fin.revPerm.trans (Tuple.sort t)
  have anti : Antitone (t ∘ σ) := by
    simp_rw [σ, coe_trans, ← Function.comp_assoc]
    exact (Tuple.monotone_sort t).comp_antitone fun _ _ ↦ Fin.rev_le_rev.mpr
  clear_value σ
  rw [← rel₄_abs neg]; change relFin4 W t = 0
  rw [← relFin4_perm' neg σ, relFin4]; simp_rw [Function.comp]
  by_cases h₃₂ : t (σ 3) = t (σ 2); · rw [h₃₂, rel₄_same₂₃ zero, smul_zero]
  by_cases h₂₁ : t (σ 2) = t (σ 1); · rw [h₂₁, rel₄_same₁₂ zero, smul_zero]
  by_cases h₁₀ : t (σ 1) = t (σ 0); · rw [h₁₀, rel₄_same₀₁ zero, smul_zero]
  rw [rel₄_of_anti_oddRec_evenRec one two oddRec evenRec (same.abs.perm _ _), smul_zero]
  exact ⟨nonneg _, (anti <| by decide).lt_of_ne h₃₂,
    (anti <| by decide).lt_of_ne h₂₁, (anti <| by decide).lt_of_ne h₁₀⟩
include neg zero one two oddRec evenRec in

theorem _root_.IsEllSequence'.of_oddRec_evenRec : IsEllSequence' W := by
  rw [isEllSequence_iff_rel₃]
  intro m n r
  rw [rel₃_iff₄, rel₄_of_oddRec_evenRec neg zero one two oddRec evenRec]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [negOnePow_two_mul, negOnePow_zero]
end Perm

end EllSequence

open EllSequence

variable {W}

lemma IsEllSequence'.map (h : IsEllSequence' W) : IsEllSequence' (f ∘ W) :=
  fun m n r => by simpa using congr_arg f (h m n r)

lemma IsDivSequence'.map (h : IsDivSequence' W) : IsDivSequence' (f ∘ W) :=
  (map_dvd f <| h · · ·)

lemma IsEllDivSequence'.map (h : IsEllDivSequence' W) : IsEllDivSequence' (f ∘ W) :=
  ⟨h.1.map f, h.2.map f⟩

namespace IsEllSequence'

open EllSequence

variable (ell : IsEllSequence' W)

include ell in
lemma oddRec (m : ℤ) : OddRec W m := (rel₃_iff_oddRec W m).mp (ell _ _ _)
include ell in
lemma evenRec (m : ℤ) : EvenRec W m := (rel₃_iff_evenRec W m).mp (ell _ _ _)

include ell in
lemma zero' [IsReduced R] : W 0 = 0 := by
  have := ell 0 0 0
  simp_rw [add_zero, sub_self, mul_assoc, ← pow_succ'] at this
  exact IsReduced.eq_zero _ ⟨_, this⟩
include ell in

lemma zero (m : ℤ) (mem : W (2 * m) ∈ R⁰) : W 0 = 0 := by
  have := ell m m (2 * m)
  rw [add_comm, sub_self, sub_self, ← two_mul, mul_comm (W _)] at this
  exact (mem_nonZeroDivisors_iff.mp mem).2 _
    ((mem_nonZeroDivisors_iff.mp (pow_mem mem 2)).2 _ this)
include ell in
lemma sub_add_neg_sub_mul_eq_zero (m n r : ℤ) :
    (W (m - n) + W (-(m - n))) * W (m + n) * W r ^ 2 = 0 := by
  have := congr($(ell m n r) + $(ell n m r))
  rw [add_comm n, ← right_distrib, ← left_distrib, mul_comm (W _)] at this
  convert this using 4 <;> ring_nf

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)

include ell one two in

lemma neg (m : ℤ) : W (-m) = - W m := by
  rw [eq_neg_iff_add_eq_zero]
  obtain ⟨m, rfl|rfl⟩ := m.even_or_odd'
  on_goal 1 => apply (mem_nonZeroDivisors_iff.mp two).2
  on_goal 2 => apply (mem_nonZeroDivisors_iff.mp one).2
  all_goals apply (mem_nonZeroDivisors_iff.mp (pow_mem one 2)).2
  · convert sub_add_neg_sub_mul_eq_zero ell (1 - m) (m + 1) 1 using 2; ring_nf
  · convert sub_add_neg_sub_mul_eq_zero ell (-m) (m + 1) 1 using 2; ring_nf
include ell one two in
protected lemma rel₄ {a b c d : ℤ} (same : HaveSameParity₄ a b c d) : rel₄ W a b c d = 0 :=
  rel₄_of_oddRec_evenRec (ell.neg one two) (ell.zero 1 two) one two
    (fun _ _ ↦ ell.oddRec _) (fun _ _ ↦ ell.evenRec _) same
include ell one two in
protected lemma net (p q r s : ℤ) : net W p q r s = 0 := by
  rw [net_eq_rel₄]
  refine ell.rel₄ one two ?_
  simp_rw [HaveSameParity₄, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul, true_and]
include ell in
include one two in
lemma invar (s m n : ℤ) : invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m :=
  invar_of_net _ (ell.net one two) _ _ _
end IsEllSequence'

variable (b c d : R)

lemma invarNum_normEDS (n : ℤ) : letI W := normEDS b c d
    invarNum W 1 n = W (n + 2) * W (n - 1) ^ 2 + W (n + 1) ^ 2 * W (n - 2) + W n ^ 3 * b ^ 2 := by
  simp [invarNum]
lemma invarNum_normEDS_two : invarNum (normEDS b c d) 1 2 = (d + b ^ 4) * b := by
  simp [invarNum, right_distrib, ← pow_succ, ← pow_add]
lemma invarDenom_normEDS_two : invarDenom (normEDS b c d) 1 2 = c * b := by simp [invarDenom]

section Complement

variable (b c d : R) (m : ℤ)

def compl₂EDSAux : R :=
  preNormEDS (b ^ 4) c d (m - 2) * preNormEDS (b ^ 4) c d (m + 1) ^ 2 * if Even m then 1 else b

@[simp] lemma compl₂EDSAux_zero : compl₂EDSAux b c d 0 = -1 := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_one : compl₂EDSAux b c d 1 = -b := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_neg_one : compl₂EDSAux b c d (-1) = 0 := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_two : compl₂EDSAux b c d 2 = 0 := by simp [compl₂EDSAux]
@[simp] lemma compl₂EDSAux_neg_two : compl₂EDSAux b c d (-2) = -d := by simp [compl₂EDSAux]

lemma compl₂EDSAux_mul_b :
    compl₂EDSAux b c d m * b = normEDS b c d (m - 2) * normEDS b c d (m + 1) ^ 2 := by
  simp_rw [compl₂EDSAux, normEDS, Int.even_add, Int.even_sub, Int.not_even_one, even_two,
    iff_false, iff_true]; split_ifs <;> ring

def compl₂EDS : R :=
  letI p := preNormEDS (b ^ 4) c d
  (p (m - 1) ^ 2 * p (m + 2) - p (m - 2) * p (m + 1) ^ 2) * if Even m then 1 else b

lemma compl₂EDSAux_neg : compl₂EDSAux b c d (-m) = -compl₂EDS b c d m - compl₂EDSAux b c d m := by
  simp_rw [compl₂EDSAux, compl₂EDS, neg_sub_left, neg_add_eq_sub, ← neg_sub m,
    preNormEDS_neg, even_neg]; ring_nf

@[simp] lemma compl₂EDS_zero : compl₂EDS b c d 0 = 2 := by simp [compl₂EDS, one_add_one_eq_two]
@[simp] lemma compl₂EDS_one : compl₂EDS b c d 1 = b := by simp [compl₂EDS]
@[simp] lemma compl₂EDS_two : compl₂EDS b c d 2 = d := by simp [compl₂EDS]

@[simp] lemma compl₂EDS_neg : compl₂EDS b c d (-m) = compl₂EDS b c d m := by
  simp_rw [compl₂EDS, neg_sub_left, neg_add_eq_sub, ← neg_sub m, preNormEDS_neg, even_neg]; ring_nf

lemma normEDS_mul_compl₂EDS :
    normEDS b c d m * compl₂EDS b c d m = normEDS b c d (2 * m) := by
  rw [show compl₂EDS b c d m = complEDS₂ b c d m from rfl]
  exact normEDS_mul_complEDS₂ b c d m

lemma normEDS_dvd_two_mul : normEDS b c d m ∣ normEDS b c d (2 * m) :=
  ⟨_, (normEDS_mul_compl₂EDS b c d m).symm⟩

lemma compl₂EDS_mul_b : letI W := normEDS b c d
    compl₂EDS b c d m * b = W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2 := by
  rw [show compl₂EDS b c d m = complEDS₂ b c d m from rfl]
  exact complEDS₂_mul_b b c d m

lemma normEDS_six_eq_mul : normEDS b c d 6 = (normEDS b c d 5 - d ^ 2) * b * c := by
  rw [show (6 : ℤ) = 2 * 3 by rfl, ← normEDS_mul_compl₂EDS, compl₂EDS, if_neg (by decide)]
  simp_rw [Int.reduceAdd, Int.reduceSub, normEDS_three, normEDS]
  rw [preNormEDS_one, preNormEDS_two, preNormEDS_four, if_neg (by decide)]
  ring

end Complement

section Map

variable {b c d}

lemma map_compl₂EDS (n : ℤ) : f (compl₂EDS b c d n) = compl₂EDS (f b) (f c) (f d) n :=
  map_complEDS₂ f b c d n

private lemma map_normEDS_fl (n : ℤ) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n :=
  map_normEDS f b c d n

lemma map_addMulSub (m n : ℤ) : f (addMulSub W m n) = addMulSub (f ∘ W) m n := by
  simp_rw [addMulSub, map_mul, Function.comp]

lemma map_rel₄ (p q r s : ℤ) : f (rel₄ W p q r s) = rel₄ (f ∘ W) p q r s := by
  simp_rw [rel₄, map_add, map_sub, map_mul, map_addMulSub]

lemma map_net (p q r s : ℤ) : f (net W p q r s) = net (f ∘ W) p q r s := by
  simp_rw [net_eq_rel₄, map_rel₄]

lemma map_invarNum (s m : ℤ) : f (invarNum W s m) = invarNum (f ∘ W) s m := by
  simp only [invarNum, map_add, map_mul, map_pow, Function.comp]

lemma map_invarDenom (s m : ℤ) : f (invarDenom W s m) = invarDenom (f ∘ W) s m := by
  simp only [invarDenom, map_mul, Function.comp_apply]

inductive Param : Type | B : Param | C : Param | D : Param

open Param MvPolynomial

noncomputable def universalNormEDS : ℤ → MvPolynomial Param ℤ := normEDS (X B) (X C) (X D)

lemma normEDS_eq_aeval : normEDS b c d = (aeval (Param.rec b c d) <| universalNormEDS ·) := by
  simp_rw [universalNormEDS, map_normEDS_fl, aeval_X]

lemma compl₂EDS_eq_aeval :
    compl₂EDS b c d =
      (aeval (Param.rec b c d) <| compl₂EDS (X (R := ℤ) B) (X C) (X D) ·) := by
  simp_rw [map_compl₂EDS, aeval_X]

end Map

section

variable {b c d} {U : ℤ → R} (ellW : IsEllSequence' W) (ellU : IsEllSequence' U)
open MvPolynomial

private lemma normEDS_of_mem_nonZeroDivisors (hb : b ∈ R⁰) : IsEllSequence' (normEDS b c d) :=
  IsEllSequence'.of_oddRec_evenRec (normEDS_neg b c d) (normEDS_zero b c d)
    (by rw [normEDS_one]; exact one_mem _) (by rwa [normEDS_two])
    (fun m _ => by simp only [OddRec, normEDS_one, one_pow, mul_one]; exact normEDS_odd b c d m)
    (fun m _ => by
      simp only [EvenRec, normEDS_one, normEDS_two, one_pow, mul_one]
      rw [normEDS_even]; ring)

protected lemma IsEllSequence'.normEDS : IsEllSequence' (normEDS b c d) := by
  rw [normEDS_eq_aeval]
  exact IsEllSequence'.map _
    (normEDS_of_mem_nonZeroDivisors <| mem_nonZeroDivisors_of_ne_zero <| X_ne_zero _)

include ellW ellU in

protected lemma IsEllSequence'.ext (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (h1 : W 1 = U 1) (h2 : W 2 = U 2) (h3 : W 3 = U 3) (h4 : W 4 = U 4) : W = U := by
  funext n
  induction n using Int.negInduction with
  | nat n =>
    refine normEDSRec ?_ h1 h2 h3 h4 (fun m h₁ h₂ h₃ h₄ h₅ ↦ ?_) (fun m h₁ h₂ h₃ h₄ ↦ ?_) n
    · rw [Nat.cast_zero, ellW.zero 1 two, ellU.zero 1 (h2 ▸ two)]
    · erw [← mul_cancel_right_mem_nonZeroDivisors (mul_mem two <| pow_mem one 2), ← mul_assoc,
        ← mul_assoc, Nat.cast_mul, Nat.cast_add, ellW.evenRec, h1, h2, ellU.evenRec]
      convert congr($h₃ * ($h₂ ^ 2 * $h₅ - $h₁ * $h₄ ^ 2)) <;> omega
    · rw [← mul_cancel_right_mem_nonZeroDivisors (pow_mem one 3)]
      erw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, ellW.oddRec, h1, ellU.oddRec]
      convert congr($h₄ * $h₂ ^ 3 - $h₁ * $h₃ ^ 3) <;> omega
  | neg ih n => rw [ellW.neg one two, ellU.neg (h1 ▸ one) (h2 ▸ two), ih]

lemma compl₂EDS_two_three_two (n : ℤ) : compl₂EDS (2 : ℤ) 3 2 n = 2 := by
  obtain rfl | hn := eq_or_ne n 0
  · exact compl₂EDS_zero ..
  · have := normEDS_mul_compl₂EDS (2 : ℤ) 3 2 n
    rwa [normEDS_two_three_two, normEDS_two_three_two, mul_comm,
      mul_cancel_right_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hn)] at this

section Divisibility

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
  (dvd₁₂ : W 1 ∣ W 2) (dvd₁₃ : W 1 ∣ W 3) (dvd₂₄ : W 2 ∣ W 4)

include ellW one two dvd₁₂ dvd₁₃ dvd₂₄ in
theorem IsEllSequence'.eq_normEDS_of_dvd :
    ∃ b c d, W = (fun n => W 1 * _root_.normEDS b c d n) := by
  obtain ⟨b, h₁₂⟩ := dvd₁₂
  obtain ⟨c, h₁₃⟩ := dvd₁₃
  obtain ⟨d, h₂₄⟩ := dvd₂₄
  have hU : IsEllSequence' (fun n => W 1 * _root_.normEDS b c d n) :=
    (IsEllSequence'.smul IsEllSequence'.normEDS (W 1))
  exact ⟨b, c, d, ellW.ext (ellU := hU) one two (by simp) (by simp [h₁₂])
    (by simp [h₁₃]) (by rw [h₂₄, h₁₂, normEDS_four]; ring)⟩

include one two in

theorem IsEllDivSequence'.eq_normEDS (h : IsEllDivSequence' W) :
    ∃ b c d, W = (fun n => W 1 * _root_.normEDS b c d n) :=
  (IsEllSequence'.eq_normEDS_of_dvd (ellW := h.1) one two (h.2 _ _ ⟨2, rfl⟩)
    (h.2 _ _ ⟨3, rfl⟩) (h.2 _ _ ⟨2, rfl⟩))

section Complement

variable (m n : ℤ)

lemma normEDS_mul_complEDS_div (hm : m ≠ 0) (n : ℤ) (dvd : m ∣ n) :
    normEDS b c d m * complEDS b c d m (n / m) = normEDS b c d n := by
  obtain ⟨n, rfl⟩ := dvd
  rw [Int.mul_ediv_cancel_left _ hm, normEDS_mul_complEDS, mul_comm]

namespace EllSequence

variable (b c d)

def redInvarNum : R :=
  compl₂EDS b c d m + normEDS b c d m ^ 3 * b + 2 * compl₂EDSAux b c d m

lemma compl₂EDS_eq_redInvarNum_sub :
    compl₂EDS b c d m =
      redInvarNum b c d m - normEDS b c d m ^ 3 * b - 2 * compl₂EDSAux b c d m := by
  rw [redInvarNum]; ring

lemma invarNum_eq_redInvarNum_mul : invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b := by
  simp_rw [redInvarNum, right_distrib, compl₂EDS_mul_b, mul_assoc 2 _ b,
    compl₂EDSAux_mul_b, invarNum_normEDS]; ring

def redInvarDenom : R :=
  letI C := complEDS b c d
  letI W := normEDS b c d
  letI r₆ := normEDS b c d 5 - d ^ 2
  if m % 6 = 0 then r₆ * C 6 (m / 6) * W (m + 1) * W (m - 1) else
  if m % 6 = 1 then r₆ * C 6 ((m - 1) / 6) * W (m + 1) * W m else
  if m % 6 = 5 then r₆ * C 6 ((m + 1) / 6) * W m * W (m - 1) else
  if m % 6 = 2 then C 3 ((m + 1) / 3) * C 2 (m / 2) * W (m - 1) else
  if m % 6 = 4 then C 3 ((m - 1) / 3) * C 2 (m / 2) * W (m + 1) else
  if m % 6 = 3 then C 3 (m / 3) * C 2 ((m - 1) / 2) * W (m + 1) else 0

lemma invarDenom_eq_redInvarDenom_mul :
    invarDenom (normEDS b c d) 1 m = redInvarDenom b c d m * b * c := by
  have h6 : (6 : ℤ) ≠ 0 := by decide
  have h3 : (3 : ℤ) ≠ 0 := by decide
  have hd (k m : ℤ) (dvd : k ∣ 6) (eq : m % 6 % k = 0) : k ∣ m :=
    Int.dvd_iff_emod_eq_zero.mpr ((Int.emod_emod_of_dvd m dvd).symm.trans eq)
  have hd2 {m} := hd 2 m ⟨3, rfl⟩
  have hd3 {m} := hd 3 m ⟨2, rfl⟩

  have dvd_sub {a b c : ℤ} (h : a % b = c) : b ∣ a - c := by
    rw [← h, Int.emod_def, sub_sub_cancel]
    apply dvd_mul_right
  have mul_eq := @normEDS_mul_complEDS_div _ _ b c d
  rw [invarDenom, redInvarDenom]; split_ifs with h h h h h h
  · rw [← mul_eq _ h6 _ (Int.dvd_of_emod_eq_zero h), normEDS_six_eq_mul]; ring
  · rw [← mul_eq _ h6 _ (dvd_sub h), normEDS_six_eq_mul]; ring
  · rw [show m + 1 = m + 6 - 5 by abel, ← mul_eq _ h6, normEDS_six_eq_mul]; ring
    exact dvd_sub (show (m + 6) % 6 = 5 by omega)
  on_goal 1 => rw [← mul_eq _ h3 _ (hd3 <| by simp [h, Int.add_emod]),
    ← mul_eq _ two_ne_zero m (hd2 <| by simp [h])]
  on_goal 2 => rw [← mul_eq _ h3 (m - 1) (hd3 <| by simp [h, Int.sub_emod]),
    ← mul_eq _ two_ne_zero m (hd2 <| by simp [h])]
  on_goal 3 => rw [← mul_eq _ h3 m (hd3 <| by simp [h]),
    ← mul_eq _ two_ne_zero (m - 1) (hd2 <| by simp [h, Int.sub_emod])]
  on_goal 4 =>
    have h0 := Int.emod_nonneg m h6
    have lt := Int.emod_lt_of_pos m (show 0 < 6 by decide)
    interval_cases m % 6 <;> contradiction
  all_goals rw [normEDS_three, normEDS_two]; ring

@[simp] lemma redInvarDenom_zero : redInvarDenom b c d 0 = 0 := by
  simp [redInvarDenom]

@[simp] lemma redInvarDenom_one : redInvarDenom b c d 1 = 0 := by
  simp [redInvarDenom]

@[simp] lemma redInvarDenom_two : redInvarDenom b c d 2 = 1 := by
  simp [redInvarDenom]

lemma map_compl₂EDSAux : f (compl₂EDSAux b c d m) = compl₂EDSAux (f b) (f c) (f d) m := by
  have mp : ∀ n : ℤ, f (preNormEDS (b ^ 4) c d n) = preNormEDS (f b ^ 4) (f c) (f d) n :=
    fun n ↦ by
      rw [show f b ^ 4 = f (b ^ 4) from (map_pow f b 4).symm]
      exact map_preNormEDS f (b ^ 4) c d n
  simp [compl₂EDSAux, apply_ite f, mp]

lemma map_redInvarNum : f (redInvarNum b c d m) = redInvarNum (f b) (f c) (f d) m := by
  have mn : ∀ n : ℤ, f (normEDS b c d n) = normEDS (f b) (f c) (f d) n :=
    fun n ↦ map_normEDS f b c d n
  simp [redInvarNum, map_compl₂EDS, mn, map_compl₂EDSAux, map_ofNat]

lemma map_redInvarDenom : f (redInvarDenom b c d m) = redInvarDenom (f b) (f c) (f d) m := by
  have mn : ∀ n : ℤ, f (normEDS b c d n) = normEDS (f b) (f c) (f d) n :=
    fun n ↦ map_normEDS f b c d n
  simp [redInvarDenom, apply_ite f, mn, map_complEDS]

end EllSequence

end Complement

protected theorem IsDivSequence'.normEDS : IsDivSequence' (normEDS b c d) := by
  rintro m _ ⟨n, rfl⟩
  rw [Nat.cast_mul, mul_comm (m : ℤ), ← normEDS_mul_complEDS]
  exact dvd_mul_right _ _

protected theorem IsEllDivSequence'.normEDS : IsEllDivSequence' (normEDS b c d) :=
  ⟨IsEllSequence'.normEDS, IsDivSequence'.normEDS⟩

include ellW one two dvd₁₂ dvd₁₃ dvd₂₄ in

lemma IsEllSequence'.isDivSequence_of_dvd : IsDivSequence' W := by
  obtain ⟨b, c, d, h⟩ := (IsEllSequence'.eq_normEDS_of_dvd (ellW := ellW) one two dvd₁₂ dvd₁₃ dvd₂₄)
  rw [h]; exact IsDivSequence'.normEDS.smul _

include ellW one two dvd₁₂ dvd₁₃ dvd₂₄ in
lemma IsEllSequence'.isEllDivSequence_of_dvd : IsEllDivSequence' W :=
  ⟨ellW, ellW.isDivSequence_of_dvd one two dvd₁₂ dvd₁₃ dvd₂₄⟩

end Divisibility

section

lemma net_normEDS (p q r s : ℤ) : net (normEDS b c d) p q r s = 0 := by
  rw [normEDS_eq_aeval, ← Function.comp_def, ← map_net,
    universalNormEDS, IsEllSequence'.normEDS.net, map_zero] <;>
    apply mem_nonZeroDivisors_of_ne_zero <;>
    simp only [normEDS_one, normEDS_two] <;>
    first
      | exact one_ne_zero
      | exact MvPolynomial.X_ne_zero _

lemma rel₄_normEDS (p q r s : ℤ) (same : HaveSameParity₄ p q r s) :
    rel₄ (normEDS b c d) p q r s = 0 := by
  rw [same.rel₄_eq_net, net_normEDS]

lemma invar_normEDS (s m n : ℤ) :
    invarNum (normEDS b c d) s m * invarDenom (normEDS b c d) s n =
      invarNum (normEDS b c d) s n * invarDenom (normEDS b c d) s m :=
  invar_of_net _ net_normEDS _ _ _

private lemma invar₂_normEDS_of_mem_nonZeroDivisors (hb : b ∈ R⁰) (m : ℤ) :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb, mul_assoc, mul_assoc, mul_comm (invarDenom _ _ _)]
  convert invar_normEDS 1 m 2 <;> simp only [invarNum_normEDS_two, invarDenom_normEDS_two]

open MvPolynomial Param in
lemma invar₂_normEDS {m : ℤ} :
    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) := by
  have := congr(aeval (Param.rec b c d) $(invar₂_normEDS_of_mem_nonZeroDivisors
    (c := X Param.C) (d := X D) (mem_nonZeroDivisors_of_ne_zero <| X_ne_zero (R := ℤ) B) m))
  rw [← universalNormEDS] at this
  simpa only [map_mul, map_invarNum, map_invarDenom,
    Function.comp_def, ← normEDS_eq_aeval, map_add, map_pow, aeval_X] using this

private lemma redInvar_normEDS_of_mem_nonZeroDivisors (hb : b ∈ R⁰) (hc : c ∈ R⁰) (m : ℤ) :
    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by
  rw [← mul_cancel_right_mem_nonZeroDivisors hb, ← mul_cancel_right_mem_nonZeroDivisors hc,
    ← invarNum_eq_redInvarNum_mul, invar₂_normEDS, invarDenom_eq_redInvarDenom_mul]
  ring

open MvPolynomial Param in
lemma redInvar_normEDS (m : ℤ) :
    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) := by
  have := congr(aeval (Param.rec b c d) $(redInvar_normEDS_of_mem_nonZeroDivisors
    (b := X (R := ℤ) B) (c := X Param.C) (d := X D) ?_ ?_ m))
  · simpa only [map_redInvarNum, map_mul, map_add, map_pow, map_redInvarDenom, aeval_X] using this
  all_goals exact mem_nonZeroDivisors_of_ne_zero (X_ne_zero _)
end

end

end PortEllSequenceCore

section PortEllSequenceUniversal

noncomputable section

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

inductive Coeff : Type | A₁ : Coeff | A₂ : Coeff | A₃ : Coeff | A₄ : Coeff | A₆ : Coeff

namespace Affine.CoordinateRing

lemma algebraMap_injective' {R : Type*} [CommRing R] (W : Affine R) :
    Function.Injective (algebraMap R W.CoordinateRing) := by
  have h : Function.Injective (algebraMap (Polynomial R) W.CoordinateRing) :=
    (injective_iff_map_eq_zero _).mpr fun p hp ↦ And.left <|
      smul_basis_eq_zero (W' := W) (q := 0) <| by
        rw [smul, smul, mul_one, Polynomial.C_0, map_zero, zero_mul, add_zero]
        exact hp
  exact h.comp Polynomial.C_injective

end Affine.CoordinateRing

namespace Univ

open scoped Polynomial Polynomial.Bivariate
open Coeff

open MvPolynomial (X) in

def curve : Affine (MvPolynomial Coeff ℤ) :=
  { a₁ := X A₁, a₂ := X A₂, a₃ := X A₃, a₄ := X A₄, a₆ := X A₆ }

lemma Δ_curve_ne_zero : curve.Δ ≠ 0 := fun h ↦ by
  simp_rw [Δ, b₂, b₄, b₆, b₈, curve] at h
  apply_fun MvPolynomial.eval (Coeff.rec 0 0 0 0 1) at h
  simp at h

abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]

protected abbrev Ring : Type := curve.CoordinateRing

protected abbrev Field : Type := FractionRing Univ.Ring

lemma Poly.two_ne_zero : (2 : Poly) ≠ 0 :=
  Polynomial.C_ne_zero.mpr <| Polynomial.C_ne_zero.mpr fun h ↦ two_ne_zero' (α := ℤ) <|
    MvPolynomial.C_injective _ _ <| by rwa [← MvPolynomial.C_0] at h

def polyToField : Poly →+* Univ.Field := (algebraMap Univ.Ring _).comp <| AdjoinRoot.mk _

lemma polyToField_apply (p : Poly) :
    polyToField p = algebraMap Univ.Ring _ (AdjoinRoot.mk _ p) := rfl

lemma algebraMap_field_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Univ.Field = polyToField.comp (algebraMap _ _) := rfl

lemma algebraMap_ring_eq_comp :
    algebraMap (MvPolynomial Coeff ℤ) Univ.Ring = (AdjoinRoot.mk _).comp (algebraMap _ _) :=
  rfl

@[simp] lemma polyToField_polynomial : polyToField curve.polynomial = 0 := by
  rw [polyToField_apply, AdjoinRoot.mk_self, map_zero]

lemma algebraMap_field_injective :
    Function.Injective (algebraMap (MvPolynomial Coeff ℤ) Univ.Field) :=
  (IsFractionRing.injective Univ.Ring Univ.Field).comp
    (Affine.CoordinateRing.algebraMap_injective' _)

abbrev pointedCurve : WeierstrassCurve Univ.Field :=
  baseChange curve Univ.Field

instance : pointedCurve.IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr <| by

    simpa only [pointedCurve, baseChange, map_Δ, map_ne_zero_iff _ algebraMap_field_injective]
      using Δ_curve_ne_zero

open Polynomial (CC)

@[simp] lemma pointedCurve_a₁ : pointedCurve.a₁ = polyToField (CC curve.a₁) := rfl
@[simp] lemma pointedCurve_a₂ : pointedCurve.a₂ = polyToField (CC curve.a₂) := rfl
@[simp] lemma pointedCurve_a₃ : pointedCurve.a₃ = polyToField (CC curve.a₃) := rfl
@[simp] lemma pointedCurve_a₄ : pointedCurve.a₄ = polyToField (CC curve.a₄) := rfl
@[simp] lemma pointedCurve_a₆ : pointedCurve.a₆ = polyToField (CC curve.a₆) := rfl

open Polynomial in
lemma equation_point : pointedCurve.toAffine.Equation (polyToField (C X)) (polyToField Y) := by
  have h := polyToField_polynomial
  simp only [Affine.polynomial, map_add, map_sub, map_mul, map_pow] at h
  rw [Affine.equation_iff', pointedCurve_a₁, pointedCurve_a₂, pointedCurve_a₃, pointedCurve_a₄,
    pointedCurve_a₆]
  linear_combination h

open Polynomial Affine in

def Affine.point : curve⟮Univ.Field⟯ :=
  .some (polyToField (C X)) (polyToField Y)
    ((pointedCurve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
      (by simpa only [pointedCurve, baseChange, map_Δ, map_ne_zero_iff _ algebraMap_field_injective]
        using Δ_curve_ne_zero)).mp equation_point)

def Jacobian.point : Jacobian.Point (WeierstrassCurve.baseChange curve Univ.Field) :=
  Jacobian.Point.fromAffine Affine.point

abbrev curvePoly : WeierstrassCurve Poly := WeierstrassCurve.baseChange curve Poly

abbrev curveRing : WeierstrassCurve Univ.Ring :=
  WeierstrassCurve.baseChange curve Univ.Ring

abbrev curveField : WeierstrassCurve Univ.Field :=
  WeierstrassCurve.baseChange curve Univ.Field

lemma curveField_eq : curveField = pointedCurve := rfl

end Univ

def cusp : Affine ℤ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }

lemma cusp_equation_one_one : cusp.Equation 1 1 := by
  simp [Affine.Equation, Affine.polynomial, cusp, Polynomial.evalEval]

open Univ
variable {R} [CommRing R] (W : WeierstrassCurve R)

def specialize : MvPolynomial Coeff ℤ →+* R :=
  (MvPolynomial.aeval <| Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆).toRingHom

lemma map_specialize : WeierstrassCurve.map Univ.curve W.specialize = W := by
  simp [specialize, curve, map]

namespace Univ

variable (x y : R)

open Polynomial (eval₂RingHom) in

def polyEval : Poly →+* R := eval₂RingHom (eval₂RingHom W.specialize x) y

open Polynomial in
lemma polyEval_apply (p : Poly) :
    polyEval W x y p = (p.map <| mapRingHom W.specialize).evalEval x y :=
  eval₂_eval₂RingHom_apply _ _ _ _

variable {W x y} (eqn : Affine.Equation W x y)

open Polynomial in

def ringEval : Univ.Ring →+* R :=
  AdjoinRoot.lift (eval₂RingHom W.specialize x) y <| by
    simp_rw [← coe_eval₂RingHom, eval₂RingHom_eval₂RingHom, RingHom.comp_apply, coe_mapRingHom]

    rw [← Affine.map_polynomial]
    simpa only [Affine.map, map_specialize, Affine.Equation, evalEval, coe_evalRingHom] using eqn

lemma ringEval_mk (p : Poly) : ringEval eqn (AdjoinRoot.mk _ p) = polyEval W x y p :=
  AdjoinRoot.lift_mk _ p

lemma ringEval_comp_mk : (ringEval eqn).comp (AdjoinRoot.mk _) = polyEval W x y :=
  RingHom.ext (ringEval_mk eqn)

lemma polyEval_comp_eq_specialize : (polyEval W x y).comp (algebraMap _ _) = W.specialize := by
  ext <;> simp [polyEval, -AddMonoidAlgebra.coe_algebraMap]

lemma ringEval_comp_eq_specialize : (ringEval eqn).comp (algebraMap _ _) = W.specialize := by
  rw [algebraMap_ring_eq_comp, ← RingHom.comp_assoc, ringEval_comp_mk, polyEval_comp_eq_specialize]

protected lemma Field.two_ne_zero : (2 : Univ.Field) ≠ 0 := by
  rw [← map_ofNat (algebraMap Univ.Ring _), map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  intro h; replace h := congr(ringEval cusp_equation_one_one $h)
  rw [map_ofNat, map_zero] at h; cases h

lemma curveRing_map_ringEval : curveRing.map (ringEval eqn) = W := by
  rw [curveRing, WeierstrassCurve.baseChange, map_map, ringEval_comp_eq_specialize, map_specialize]

end Univ

end WeierstrassCurve

end

end PortEllSequenceUniversal

section PortEllSequenceDivisionPolys

open Polynomial
open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

namespace WeierstrassCurve

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

noncomputable section

def invar : R[X] := 6 * X ^ 2 + C W.b₂ * X + C W.b₄

def ψc : ℤ → R[X][Y] := compl₂EDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)

open Affine (polynomial polynomialX polynomialY negPolynomial)
open EllSequence

lemma C_Ψ₃_eq :
    C W.Ψ₃ = (3 * C X + CC W.a₂) * C W.Ψ₂Sq - polynomialX W ^ 2
      + CC W.a₁ * W.ψ₂ * polynomialX W - CC W.a₁ ^ 2 * polynomial W := by
  simp_rw [Ψ₃, Ψ₂Sq, polynomial, polynomialX, ψ₂, polynomialY, b₂, b₄, b₆, b₈, CC]; C_simp; ring

lemma preΨ₄_add_Ψ₂Sq_sq : W.preΨ₄ + W.Ψ₂Sq ^ 2 = W.invar * W.Ψ₃ := by
  rw [preΨ₄, Ψ₂Sq, invar, Ψ₃]
  linear_combination (norm := (C_simp; ring_nf)) congr(C $W.b_relation) * (@X R _) ^ 2

lemma preΨ₄_add_ψ₂_pow_four : C W.preΨ₄ + W.ψ₂ ^ 4 =
    C (W.invar * W.Ψ₃) + 8 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq) := by
  simp_rw [show 4 = 2 * 2 by rfl, pow_mul, ψ₂_sq, add_sq,
    ← add_assoc, ← C_pow, ← C_add, preΨ₄_add_Ψ₂Sq_sq]; C_simp; ring

lemma φ_mul_ψ (n : ℤ) : W.φ n * W.ψ n = C X * W.ψ n ^ 3 - invarDenom W.ψ 1 n := by
  rw [WeierstrassCurve.φ, invarDenom]; ring

protected def ωe (n : ℤ) : R[X][Y] :=
  redInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
    ((CC W.a₁ * polynomialY W - polynomialX W) * C W.Ψ₃
      + 4 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq))
  - compl₂EDSAux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + negPolynomial W * W.ψ n ^ 3

lemma ωe_spec (n : ℤ) :
    2 * W.ωe n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = W.ψc n := by
  have hψ : W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl
  rw [ψc, compl₂EDS_eq_redInvarNum_sub, redInvar_normEDS, preΨ₄_add_ψ₂_pow_four,
    mul_assoc (C _), φ_mul_ψ, hψ, invarDenom_eq_redInvarDenom_mul, WeierstrassCurve.ωe, ← hψ,
    invar, b₂, b₄, ψ₂, Affine.polynomialY, Affine.polynomialX, Affine.negPolynomial]
  C_simp; ring

lemma two_mul_ωe (n : ℤ) :
    2 * W.ωe n = W.ψc n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3 := by
  rw [← ωe_spec]; abel

lemma ψc_spec (n : ℤ) : W.ψ n * W.ψc n = W.ψ (2 * n) := normEDS_mul_compl₂EDS _ _ _ _

@[simp] lemma ωe_zero : W.ωe 0 = 1 := by simp [WeierstrassCurve.ωe]

@[simp] lemma ωe_one : W.ωe 1 = Y := by simp [WeierstrassCurve.ωe, ψ₂, ← Affine.Y_sub_polynomialY]

@[simp] lemma ψc_neg (n : ℤ) : W.ψc (-n) = W.ψc n := by simp [ψc]

end

section Map

variable (f : R →+* S)

lemma map_ψc (n : ℤ) : (W.map f).ψc n = (W.ψc n).map (mapRingHom f) := by
  simp only [ψc, ← coe_mapRingHom, map_compl₂EDS, map_ψ₂, map_Ψ₃, map_preΨ₄]
  simp only [coe_mapRingHom, map_C]

lemma map_invar : (W.map f).invar = W.invar.map f := by
  simp only [invar, map_b₂, map_b₄]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_ofNat,
    map_C, map_X]

open Affine EllSequence in
lemma map_ωe (n : ℤ) : (W.map f).ωe n = (W.ωe n).map (mapRingHom f) := by
  simp_rw [WeierstrassCurve.ωe, ← coe_mapRingHom, map_add, map_sub, map_mul, map_redInvarDenom,
    map_compl₂EDSAux, map_polynomial, map_polynomialX, map_polynomialY, map_negPolynomial,
    map_ψ₂, map_Ψ₃, map_preΨ₄, map_Ψ₂Sq, map_ψ]; simp

end Map

end WeierstrassCurve

end PortEllSequenceDivisionPolys

section PortEllSequenceZSMul

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)

noncomputable section

variable {x y : R}

namespace Univ

lemma evalEval_ψ₂ : W.ψ₂.evalEval x y = polyEval W x y curve.ψ₂ := by
  simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]

lemma evalEval_Ψ₃ : (C W.Ψ₃).evalEval x y = polyEval W x y (C curve.Ψ₃) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_Ψ₃, map_specialize]

lemma evalEval_preΨ₄ : (C W.preΨ₄).evalEval x y = polyEval W x y (C curve.preΨ₄) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_preΨ₄, map_specialize]

variable {m n : ℤ}

lemma evalEval_ψ : (W.ψ n).evalEval x y = polyEval W x y (curve.ψ n) := by
  simp_rw [polyEval_apply, ← map_ψ, map_specialize]

lemma evalEval_φ : (W.φ n).evalEval x y = polyEval W x y (curve.φ n) := by
  simp_rw [polyEval_apply, ← map_φ, map_specialize]

lemma evalEval_ωe : (W.ωe n).evalEval x y =  polyEval W x y (curve.ωe n) := by
  simp_rw [polyEval_apply, ← map_ωe, map_specialize]

open WeierstrassCurve (ψ φ ωe)

lemma cusp_ψ₂ : cusp.ψ₂ = 2 * Y := by
  simp [cusp, ψ₂, Affine.polynomialY, map_ofNat]

lemma cusp_Ψ₃ : cusp.Ψ₃ = 3 * X ^ 4 := by simp [cusp, Ψ₃, b₂, b₄, b₆, b₈]
lemma cusp_preΨ₄ : cusp.preΨ₄ = 2 * X ^ 6 := by simp [cusp, preΨ₄, b₂, b₄, b₆, b₈]

lemma polyEval_cusp_ψ : polyEval cusp 1 1 (curve.ψ n) = n := by
  rw [ψ, map_normEDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄, cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄]
  simp [evalEval, normEDS_two_three_two]

lemma polyEval_cusp_φ : polyEval cusp 1 1 (curve.φ n) = 1 := by
  simp_rw [φ, map_sub, map_mul, map_pow, polyEval_cusp_ψ, polyEval]
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_X]; ring

lemma polyEval_cusp_ψc : polyEval cusp 1 1 (curve.ψc n) = 2 := by
  rw [ψc, map_compl₂EDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄]
  simp [cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄, evalEval, compl₂EDS_two_three_two]

lemma polyEval_cusp_ωe : polyEval cusp 1 1 (curve.ωe n) = 1 := by
  have := congr(polyEval cusp 1 1 $(curve.two_mul_ωe n))
  simp_rw [map_sub, map_mul, map_ofNat, polyEval_cusp_ψc] at this
  simpa [cusp, polyEval, specialize, curve] using this

abbrev ψᵤ (n : ℤ) : Univ.Field := polyToField (curve.ψ n)

lemma ψᵤ_eq_normEDS :
    ψᵤ = normEDS
      (polyToField curve.ψ₂) (polyToField <| C curve.Ψ₃) (polyToField <| C curve.preΨ₄) := by
  ext; rw [← map_normEDS]; rfl

lemma isEllSequence_ψᵤ : IsEllSequence' ψᵤ := by rw [ψᵤ_eq_normEDS]; exact IsEllSequence'.normEDS
lemma net_ψᵤ (p q r s) : EllSequence.net ψᵤ p q r s = 0 := by rw [ψᵤ_eq_normEDS]; apply net_normEDS

lemma ψᵤ_ne_zero (h0 : n ≠ 0) : ψᵤ n ≠ 0 := fun h ↦ by
  rw [ψᵤ, polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_ψ, map_zero] at h
  exact h0 h

lemma polyToField_φ_ne_zero : polyToField (curve.φ n) ≠ 0 := fun h ↦ by
  rw [polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_φ, map_zero] at h
  exact one_ne_zero h

lemma polyToField_ψ₂Sq : polyToField (C curve.Ψ₂Sq) = ψᵤ 2 ^ 2 := by
  rw [← map_pow, ψ_two, ψ₂_sq, map_add, map_mul, polyToField_polynomial, mul_zero, add_zero]

namespace Affine

variable (n)

def smulX : Univ.Field := polyToField (curve.φ n) / (ψᵤ n) ^ 2

def smulY : Univ.Field := polyToField (curve.ωe n) / (ψᵤ n) ^ 3
variable {n}

@[simp] lemma smulX_zero : smulX 0 = 0 := by simp [smulX, ψᵤ]
@[simp] lemma smulY_zero : smulY 0 = 0 := by simp [smulY, ψᵤ]
@[simp] lemma smulX_one : smulX 1 = polyToField (C X) := by simp [smulX, ψᵤ]
@[simp] lemma smulY_one : smulY 1 = polyToField Y := by simp [smulY, ψᵤ]

lemma smulX_eq (hn : n ≠ 0) :
    smulX n = smulX 1 - ψᵤ (n + 1) * ψᵤ (n - 1) / (ψᵤ n) ^ 2 := by
  rw [smulX, smulX_one, φ, map_sub, sub_div, map_mul, map_pow, mul_div_cancel_right₀, map_mul]
  exact pow_ne_zero _ (ψᵤ_ne_zero hn)

lemma smulX_two : smulX 2 = smulX 1 - ψᵤ 3 / (ψᵤ 2) ^ 2 := by
  simp [smulX_eq two_ne_zero, ψᵤ]

lemma smulX_sub_smulX (hm : m ≠ 0) (hn : n ≠ 0) :
    smulX m - smulX n = (ψᵤ (n + m) * ψᵤ (n - m)) / (ψᵤ n * ψᵤ m) ^ 2 := by
  rw [smulX_eq hm, smulX_eq hn, sub_sub_sub_cancel_left, div_sub_div]
  · rw [mul_pow]; congr; convert (isEllSequence_ψᵤ n m 1).symm using 1
    · ring
    · simp [ψᵤ]
  all_goals exact pow_ne_zero _ (ψᵤ_ne_zero <| by assumption)

lemma smulX_sub_sub_smulX_add (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    smulX (n - m) - smulX (n + m) = (ψᵤ (2 * n) * ψᵤ (2 * m)) / (ψᵤ (n + m) * ψᵤ (n - m)) ^ 2 := by
  rw [smulX_sub_smulX sub_ne add_ne]; ring_nf

lemma smulX_neg : smulX (-n) = smulX n := by simp_rw [smulX, φ_neg, ψᵤ, ψ_neg, map_neg, neg_sq]

lemma smulX_ne_zero (h0 : n ≠ 0) : smulX n ≠ 0 :=
  div_ne_zero polyToField_φ_ne_zero (pow_ne_zero _ <| ψᵤ_ne_zero h0)

lemma smulX_ne_smulX (ne : m ≠ n) (ne_neg : m ≠ -n) : smulX m ≠ smulX n := by
  obtain rfl | hm := eq_or_ne m 0
  · rw [smulX_zero]; exact (smulX_ne_zero ne.symm).symm
  obtain rfl | hn := eq_or_ne n 0
  · rw [smulX_zero]; exact smulX_ne_zero ne
  rw [← sub_ne_zero, smulX_sub_smulX hm hn]
  rw [ne_comm, ← sub_ne_zero] at ne
  rw [Ne, ← add_eq_zero_iff_eq_neg, add_comm] at ne_neg
  refine div_ne_zero (mul_ne_zero ?_ ?_) (pow_ne_zero _ <| mul_ne_zero ?_ ?_) <;>
    apply ψᵤ_ne_zero <;> assumption

lemma smulX_eq_smulX_iff : smulX m = smulX n ↔ m = n ∨ m = -n := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · contrapose! h; exact smulX_ne_smulX h.1 h.2
  · rintro (rfl|rfl); exacts [rfl, smulX_neg]

private lemma smulY_sub_negY_aux {G} [_root_.Field G] {a₁ a₃ x y z : G} (h0 : z ≠ 0) :
    y / z ^ 3 - (-(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃) =
      z * (2 * y + a₁ * x * z + a₃ * z ^ 3) / z ^ 4 := by
  field_simp; ring

lemma smulY_sub_negY (h0 : n ≠ 0) :
    smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n) = ψᵤ (2 * n) / (ψᵤ n) ^ 4 := by
  simp_rw [Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, smulY, ψᵤ, ← ψc_spec, ← ωe_spec,
    map_mul, map_add, map_mul, map_pow, map_ofNat]
  exact smulY_sub_negY_aux (ψᵤ_ne_zero h0)

lemma smulY_one_sub_negY :
    smulY 1 - pointedCurve.toAffine.negY (smulX 1) (smulY 1) = ψᵤ 2 := by
  rw [smulY_sub_negY one_ne_zero, mul_one, ψᵤ, ψᵤ, ψ_one, map_one, one_pow, div_one]

lemma smulY_one_ne_negY : smulY 1 ≠ pointedCurve.toAffine.negY (smulX 1) (smulY 1) := by
  rw [← sub_ne_zero, smulY_one_sub_negY]; exact ψᵤ_ne_zero two_ne_zero

def slopeOne : Univ.Field :=
  pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)

lemma slopeOne_eq_neg_div : slopeOne = -polyToField curve.polynomialX / ψᵤ 2 := by
  rw [slopeOne, Affine.slope_of_Y_ne rfl smulY_one_ne_negY, smulY_one_sub_negY, Affine.polynomialX]
  congr
  simp [algebraMap_field_eq_comp, Polynomial.algebraMap_apply, map_ofNat,
    -AddMonoidAlgebra.coe_algebraMap]

private lemma addX_smul_one_smul_one_aux {G} [_root_.Field G] {a₁ a₂ x dx dy : G} (h0 : dy ≠ 0) :
    (-dx / dy) ^ 2 + a₁ * (-dx / dy) - a₂ - x - x - x =
      (dx ^ 2 - a₁ * dx * dy - (3 * x + a₂) * dy ^ 2) / dy ^ 2 := by

  field_simp; ring

lemma addX_smul_one_smul_one :
    pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2 := .symm <| by
  rw [smulX_two, Affine.addX, sub_eq_neg_add, ← eq_sub_iff_add_eq, ← neg_div _ (polyToField _),
    slopeOne_eq_neg_div, addX_smul_one_smul_one_aux (ψᵤ_ne_zero two_ne_zero)]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, polyToField_ψ₂Sq, ψᵤ,
    ψ_two, ψ_three, C_Ψ₃_eq, polyToField_polynomial, pointedCurve_a₁, pointedCurve_a₂, smulX_one]
  ring

private lemma addY_smul_one_smul_one_aux {G} [_root_.Field G]
    {a₁ a₃ dx dy x y ψ₃ t : G} (h0 : dy ≠ 0) :
    ((a₁ * dy - dx) * ψ₃ + 0 * t + (-y - (a₁ * x + a₃)) * dy ^ 3) / dy ^ 3 =
      -(-dx / dy * (x - ψ₃ / dy ^ 2 - x) + y) - a₁ * (x - ψ₃ / dy ^ 2) - a₃ := by
  field_simp; ring

open EllSequence in
lemma addY_smul_one_smul_one :
    pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2 := .symm <| by
  rw [smulY, ωe, redInvarDenom_two, one_mul, compl₂EDSAux_two, sub_zero, Affine.addY,
    Affine.negAddY, addX_smul_one_smul_one, smulX_two, Affine.negY, Affine.negPolynomial,
    slopeOne_eq_neg_div, ← ψ₂, ← ψ_two, smulX_one, smulY_one, ψᵤ, ψᵤ, ψ_three]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, polyToField_polynomial, mul_zero]
  exact addY_smul_one_smul_one_aux (ψᵤ_ne_zero two_ne_zero)

private lemma smulY_neg_aux {G} [_root_.Field G] {a₁ a₃ x y z : G} (hz : z ≠ 0) :
    (y + a₁ * x * z + a₃ * z ^ 3) / (-z) ^ 3 = -(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃ := by
  rw [neg_pow]; field_simp; ring

open Polynomial (CC) in

lemma ωe_neg' : curve.ωe (-n) =
    curve.ωe n + CC curve.a₁ * curve.φ n * curve.ψ n + CC curve.a₃ * curve.ψ n ^ 3 := by
  rw [← mul_cancel_left_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero Poly.two_ne_zero)]
  simp_rw [left_distrib, two_mul_ωe, ψc_neg, ψ_neg, φ_neg]; ring

lemma smulY_neg (h0 : n ≠ 0) :
    smulY (-n) = pointedCurve.toAffine.negY (smulX n) (smulY n) := by
  simp only [Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, smulY, ψ_neg, ωe_neg',
    map_add, map_neg, map_mul, map_pow, ψᵤ]
  exact smulY_neg_aux (ψᵤ_ne_zero h0)

private lemma smulX_add_aux {G} [_root_.Field G] {m n m₂ n₂ a s : G}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    n₂ / n ^ 4 * (m₂ / m ^ 4) / (a * s / (n * m) ^ 2) ^ 2 = n₂ * m₂ / (a * s) ^ 2 := by
  field_simp

lemma smulX_add (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    let ψ₂ x y := y - pointedCurve.toAffine.negY x y
    smulX (n + m) = smulX (n - m) -
      ψ₂ (smulX n) (smulY n) * ψ₂ (smulX m) (smulY m) / (smulX m - smulX n) ^ 2 := by
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', smulX_sub_sub_smulX_add add_ne sub_ne]
  simp_rw [smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hm hn]
  apply smulX_add_aux <;> apply ψᵤ_ne_zero <;> assumption

private lemma smulY_add_sub_negY_aux {G} [_root_.Field G] {m n m₂ n₂ a s am an : G}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    (m₂ / m ^ 4 * (an * m / (a * n) ^ 2) - n₂ / n ^ 4 * (am * n / (a * m) ^ 2))
      / (a * s / (n * m) ^ 2)
      = (an * m₂ * n - am * n₂ * m) * a / (s * n * m) / a ^ 4 := by

  field_simp

lemma smulY_add_sub_negY (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    let ψ₂ x y := y - pointedCurve.toAffine.negY x y
    ψ₂ (smulX (n + m)) (smulY (n + m)) =
      (ψ₂ (smulX m) (smulY m) * (smulX n - smulX (n + m))
        - ψ₂ (smulX n) (smulY n) * (smulX m - smulX (n + m))) / (smulX m - smulX n) := by
  simp_rw [smulY_sub_negY add_ne, smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hn add_ne,
    smulX_sub_smulX hm add_ne, smulX_sub_smulX hm hn, add_sub_cancel_left, add_sub_cancel_right]
  rw [smulY_add_sub_negY_aux]
  · congr; rw [eq_div_iff]
    · linear_combination (norm := ring_nf) (EllSequence.net_add_sub_iff _ n m).mp (net_ψᵤ _ _ _ _)
    apply_rules [mul_ne_zero, ψᵤ_ne_zero]
  all_goals apply ψᵤ_ne_zero; assumption

open Affine.Point

open WeierstrassCurve.Affine in
instance : AddGroup (curve⟮Univ.Field⟯) := inferInstance

theorem zsmul_point_eq_smulX_smulY : n ≠ 0 →
    ∃ h : Affine.Nonsingular curveField (smulX n) (smulY n),
      n • Affine.point = .some (smulX n) (smulY n) h := by

  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih h0 ↦ ?_
    obtain _|_|_|n := n
    · exact (h0 rfl).elim
    · simp_rw [zero_add, Nat.cast_one, one_zsmul, smulX_one, smulY_one]
      exact ⟨(pointedCurve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
        (by simpa only [pointedCurve, baseChange, map_Δ,
          map_ne_zero_iff _ algebraMap_field_injective]
          using Δ_curve_ne_zero)).mp equation_point, rfl⟩
    all_goals obtain ⟨ns, eq⟩ := ih 1 (by omega) one_ne_zero
    · erw [← addX_smul_one_smul_one, ← addY_smul_one_smul_one, zero_add, add_zsmul _ 1 1, eq]
      exact ⟨Affine.nonsingular_add ns ns fun h ↦ smulY_one_ne_negY h.2,
        dif_neg fun h ↦ smulY_one_ne_negY h.2⟩
    set n2 := n + 1 + 1
    obtain ⟨ns1, eq1⟩ := ih (n + 1) (by omega) (by omega)
    obtain ⟨ns2, eq2⟩ := ih n2 (by omega) (by omega)
    have ne : smulX n2 ≠ smulX 1 := smulX_ne_smulX (by omega) (by omega)
    simp_rw [show (n + 1 : ℕ) = n2 + (-1 : ℤ) by omega, add_zsmul, neg_smul] at eq1
    let _U := pointedCurve.toAffine
    erw [eq2, eq, add_of_X_ne ne, Affine.Point.some.injEq] at eq1
    let L := _U.slope (smulX n2) (smulX 1) (smulY n2) (smulY 1)
    have X_eq : smulX (n2 + 1 : ℕ) = _U.addX (smulX n2) (smulX 1) L := by
      rw [Nat.cast_add, Nat.cast_one, smulX_add one_ne_zero (by omega) (by omega) (by omega),
        Affine.addX_eq_addX_negY_sub _ _ ne, sub_eq_add_neg (n2 : ℤ), ← eq1.1]; rfl
    have Y_eq : smulY (n2 + 1 : ℕ) = _U.addY (smulX n2) (smulX 1) (smulY n2) L := by
      rw [← mul_cancel_left_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero Field.two_ne_zero),
        ← add_right_cancel_iff (a := _U.a₁ * smulX (n2 + 1 : ℕ) + _U.a₃)]
      convert smulY_add_sub_negY (n := n2) one_ne_zero (by omega) (by omega) (by omega) using 1
      · simp_rw [Affine.negY, Nat.cast_add]; simp only [_U]; ring_nf
      convert _U.addY_sub_negY_addY (smulY n2) (smulY 1) ne using 1
      · rw [Affine.negY, ← X_eq]; ring
      · rw [← X_eq]; rfl
    rw [X_eq, Y_eq, n2.cast_add, add_zsmul, eq, eq2]
    exact ⟨Affine.nonsingular_add ns2 ns fun h ↦ (ne h.1).elim, add_of_X_ne ne⟩
  | neg hn n =>
    rw [neg_ne_zero]; intro h0
    obtain ⟨ns, eq⟩ := hn n h0
    simp_rw [smulX_neg, smulY_neg h0, neg_smul, eq, neg_some]
    exact ⟨(Affine.nonsingular_neg ..).mpr ns, trivial⟩

lemma nonsingular_smulX_smulY (hn : n ≠ 0) : Affine.Nonsingular curveField (smulX n) (smulY n) := by
  exact (zsmul_point_eq_smulX_smulY hn).1

lemma zsmul_point_ne_zero (h0 : n ≠ 0) : n • Affine.point ≠ 0 := by
  obtain ⟨ns, eq⟩ := zsmul_point_eq_smulX_smulY h0
  rw [eq]; exact Affine.Point.some_ne_zero ns

end Affine

namespace Jacobian

open WeierstrassCurve.Jacobian

open Point in
lemma zsmul_point_ne_zero (h0 : n ≠ 0) : n • Jacobian.point ≠ 0 := by
  rw [Jacobian.point, ← toAffineAddEquiv_symm_apply, ← map_zsmul (toAffineAddEquiv _).symm,
    Ne, map_eq_zero_iff _ (toAffineAddEquiv _).symm.injective]
  exact Affine.zsmul_point_ne_zero h0

lemma zsmul_point_ne (h : m ≠ n) : m • Jacobian.point ≠ n • Jacobian.point := by
  rw [← sub_ne_zero, sub_eq_add_neg, ← sub_zsmul]
  exact zsmul_point_ne_zero (sub_ne_zero.mpr h)

lemma point_point : Jacobian.point.point = ⟦![polyToField (C X), polyToField Y, 1]⟧ := rfl

abbrev smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, curve.ωe n, curve.ψ n]

abbrev smulRing (n : ℤ) : Fin 3 → Univ.Ring := AdjoinRoot.mk _ ∘ smulPoly n

abbrev smulField (n : ℤ) : Fin 3 → Univ.Field := polyToField ∘ smulPoly n

lemma algebraMap_comp_smulRing (n : ℤ) : algebraMap _ _ ∘ smulRing n = smulField n := by
  ext i; fin_cases i <;> rfl

theorem zsmul_point_eq_smulField : (n • Jacobian.point).point = ⟦smulField n⟧ := by
  rw [← fin3_def (smulField n), smulField, smulPoly]
  simp_rw [Function.comp, fin3_def_ext]
  obtain rfl | hn := eq_or_ne n 0
  · simp_rw [zero_zsmul, φ_zero, ωe_zero, ψ_zero, map_zero, map_one]; rfl
  obtain ⟨ns, eq⟩ := Affine.zsmul_point_eq_smulX_smulY hn
  change (n • (Point.toAffineAddEquiv _).symm Affine.point).point = _
  rw [← map_zsmul, eq]
  have := ψᵤ_ne_zero hn
  refine Quotient.sound ⟨.mk0 _ (inv_ne_zero this), ?_⟩
  simp_rw [Units.smul_def, Jacobian.smul_fin3]
  ext i; fin_cases i <;>
    simp only [Units.val_mk0, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    field_simp [Affine.smulX, Affine.smulY, this] <;> rfl

lemma dblZ_smulPoly : dblZ curvePoly (smulPoly n) = curve.ψ (2 * n) := by
  simp_rw [dblZ, smulPoly, negY, fin3_def_ext, curvePoly, baseChange, map, coe_algebraMap_eq_CC]
  rw [← ψc_spec _ n]; congr; convert curve.ωe_spec n using 1; ring

lemma nonsingular_smulField : Nonsingular curveField (smulField n) := by
  simpa only [zsmul_point_eq_smulField, Jacobian.nonsingularLift_iff]
    using (n • Jacobian.point).nonsingular

lemma dblXYZ_smulField : dblXYZ curveField (smulField n) = smulField (2 * n) := by
  obtain rfl | hn := eq_or_ne n 0
  ·

    rw [mul_zero]
    have h0 : smulField (0 : ℤ) = ![1, 1, 0] := by
      ext i
      fin_cases i <;> simp [smulField, smulPoly, φ_zero, ωe_zero, ψ_zero]
    rw [h0, dblXYZ_of_Z_eq_zero equation_zero rfl]
    simp

  have h2 : ((2 : ℤ) • (n • Jacobian.point)).point =
      ⟦dblXYZ curveField (smulField n)⟧ := by
    rw [two_zsmul, Point.add_point, zsmul_point_eq_smulField, addMap_eq, add_self]
  refine (equiv_iff_eq_of_Z_eq ?_ (ψᵤ_ne_zero <| mul_ne_zero two_ne_zero hn)).mp
    (Quotient.exact ?_)
  · simp only [smulField, smulPoly, fin3_def_ext, Function.comp, ← dblZ_smulPoly]
    exact map_dblZ (W' := curvePoly) polyToField _
  rw [← h2, ← mul_zsmul]
  exact zsmul_point_eq_smulField

lemma dblXYZ_smulRing : dblXYZ curveRing (smulRing n) = smulRing (2 * n) :=
  (IsFractionRing.injective _ Univ.Field).comp_left <| by
    simp_rw [← map_dblXYZ]; exact dblXYZ_smulField

lemma addZ_smulPoly : addZ (smulPoly m) (smulPoly n) = curve.ψ (n + m) * curve.ψ (n - m) := by
  have hES : IsEllSequence' (WeierstrassCurve.ψ curve) := IsEllSequence'.normEDS
  simp_rw [addZ, smulPoly, φ]; convert (hES n m 1).symm using 1
  · simp only [fin3_def_ext]; ring
  · rw [ψ_one]; ring

lemma ωe_neg_eq_neg_negY : curve.ωe (-n) = -negY curvePoly (smulPoly n) := by

  simp_rw [Affine.ωe_neg' (n := n), negY, smulPoly, fin3_def_ext, curvePoly, baseChange, map,
    coe_algebraMap_eq_CC]
  ring

lemma smulPoly_neg : smulPoly (-n) = (-1 : Poly) • neg curvePoly (smulPoly n) := by
  simp only [smulPoly, φ_neg, ωe_neg_eq_neg_negY, ψ_neg, neg, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val, smul_fin3, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_one,
    Matrix.vecCons_inj, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> ring

lemma smulRing_neg : smulRing (-n) = (-1 : Univ.Ring) • neg curveRing (smulRing n) := by
  simp_rw [smulRing, smulPoly_neg, Jacobian.comp_smul, ← Jacobian.map_neg, map_neg, map_one]; rfl

lemma smulField_neg : smulField (-n) = (-1 : Univ.Field) • neg curveField (smulField n) := by
  rw [smulField, smulPoly_neg]
  refine (Jacobian.comp_smul (R := Poly) (S := Univ.Field) polyToField _ _).trans ?_
  rw [map_neg, map_one]
  exact congrArg _
    (Jacobian.map_neg (R := Poly) (S := Univ.Field) (W' := curvePoly) polyToField _).symm

lemma smulPoly_zero : smulPoly 0 = ![1, 1, 0] := by simp [smulPoly]
lemma smulField_zero : smulField 0 = ![1, 1, 0] := by simp [smulField, smulPoly_zero, comp_fin3]

lemma addXYZ_smulField :
    addXYZ curveField (smulField m) (smulField n) =
      polyToField (curve.ψ (n - m)) • smulField (n + m) := by
  obtain rfl | h := eq_or_ne m n
  · rw [sub_self, ψ_zero, map_zero, smul_fin3,
      addXYZ_self nonsingular_smulField.1, zero_pow two_ne_zero, zero_pow (by decide)]
    simp_rw [zero_mul]
  obtain rfl | ne_neg := eq_or_ne n (-m)
  · rw [← one_smul (M := Univ.Field) (smulField m), smulField_neg, neg_add_cancel,
      addXYZ_smul, one_mul, neg_one_sq (R := Univ.Field), addXYZ_neg nonsingular_smulField.1,
      one_smul, ← neg_add', ← two_mul, ψ_neg, map_neg, ← dblZ_smulPoly, smulField_zero]
    congr 2
    exact map_dblZ (W' := curvePoly) polyToField _
  have hne : ¬ smulField m ≈ smulField n := fun heq ↦ zsmul_point_ne h <| by
    rw [Point.ext_iff, zsmul_point_eq_smulField, zsmul_point_eq_smulField]
    exact Quotient.sound heq
  have key : (m • Jacobian.point + n • Jacobian.point).point =
      ⟦addXYZ curveField (smulField m) (smulField n)⟧ := by
    rw [Point.add_point, zsmul_point_eq_smulField, zsmul_point_eq_smulField, addMap_eq,
      add_of_not_equiv hne]
  erw [← equiv_iff_eq_of_Z_eq]
  · exact Quotient.exact (by
      rw [smul_eq _ (ψᵤ_ne_zero <| sub_ne_zero_of_ne h.symm).isUnit,
        ← zsmul_point_eq_smulField, add_comm, add_zsmul, key])
  · conv_rhs => rw [smulField, comp_fin3, smul_fin3, (fin3_def_ext _ _ _).2.2, mul_comm]
    simp_rw [addXYZ, fin3_def_ext, ← map_mul, ← addZ_smulPoly]
    exact map_addZ polyToField (smulPoly m) (smulPoly n)
  · rw [(smul_fin3_ext _ _).2.2]
    apply mul_ne_zero <;> apply ψᵤ_ne_zero <;> omega

lemma addXYZ_smulRing :
    addXYZ curveRing (smulRing m) (smulRing n) =
      AdjoinRoot.mk curve.polynomial (curve.ψ (n - m)) • smulRing (n + m) :=
  (IsFractionRing.injective Univ.Ring Univ.Field).comp_left <| by
    simp_rw [← map_addXYZ, Jacobian.comp_smul]; exact addXYZ_smulField

lemma addXYZ_smulField₁ :
    addXYZ curveField (smulField n) (smulField (n + 1)) = smulField (2 * n + 1) := by
  rw [addXYZ_smulField, add_sub_cancel_left, ψ_one, map_one, one_smul, two_mul, add_comm, add_assoc]

lemma addXYZ_smulRing₁ :
    addXYZ curveRing (smulRing n) (smulRing (n + 1)) = smulRing (2 * n + 1) := by
  rw [addXYZ_smulRing, add_sub_cancel_left, ψ_one, map_one, one_smul, two_mul, add_comm, add_assoc]

end Jacobian

end Univ

variable (x y) in

abbrev smulEval (n : ℤ) : Fin 3 → R := evalEval x y ∘ ![W.φ n, W.ωe n, W.ψ n]

variable {W} (eqn : W.toAffine.Equation x y)

open Univ Jacobian

lemma ringEval_comp_smulRing (n : ℤ) : ringEval eqn ∘ smulRing n = smulEval W x y n := by

  conv_rhs => rw [smulEval, ← W.map_specialize, map_φ, map_ωe, map_ψ, ← coe_mapRingHom,
    ← Jacobian.comp_fin3, ← Function.comp_assoc, ← smulPoly, ← coe_evalEvalRingHom,
    ← RingHom.coe_comp, ← eval₂RingHom_eval₂RingHom]
  rw [smulRing, ← Function.comp_assoc, ← RingHom.coe_comp, ringEval_comp_mk, polyEval]

lemma ringEval_ψ (n : ℤ) :
    ringEval eqn (AdjoinRoot.mk _ <| curve.ψ n) = evalEval x y (W.ψ n) :=
  congr_fun (ringEval_comp_smulRing eqn n) 2

include eqn in
lemma dblXYZ_smulEval (n : ℤ) : dblXYZ W (smulEval W x y n) = smulEval W x y (2 * n) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← dblXYZ_smulRing, ← map_dblXYZ, curveRing_map_ringEval]

include eqn in
lemma addXYZ_smulEval (m n : ℤ) :
    addXYZ W (smulEval W x y m) (smulEval W x y n) =
      evalEval x y (W.ψ (n - m)) • smulEval W x y (n + m) := by

  simp_rw [← ringEval_comp_smulRing eqn, ← ringEval_ψ eqn]
  rw [← Jacobian.comp_smul, ← addXYZ_smulRing, ← map_addXYZ]

  simp_rw [curveRing_map_ringEval]

include eqn in
lemma addXYZ_smulEval₁ (n : ℤ) :
    addXYZ W (smulEval W x y n) (smulEval W x y (n + 1)) = smulEval W x y (2 * n + 1) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← addXYZ_smulRing₁, ← map_addXYZ, curveRing_map_ringEval]

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

open Univ

theorem zsmul_eq_smulEval {x y : F} (h : Affine.Nonsingular W x y) (n : ℤ) :
    (n • Point.fromAffine (Affine.Point.some x y h)).point = ⟦smulEval W x y n⟧ := by

  have add_point_eq : ∀ (P Q : Jacobian.Point W) (P' Q' : Fin 3 → F),
      P.point = ⟦P'⟧ → Q.point = ⟦Q'⟧ → (P + Q).point = ⟦Jacobian.add W P' Q'⟧ := by
    intro P Q P' Q' hP hQ
    rw [Point.add_point, hP, hQ, addMap_eq]
  have two_zsmul_point : ∀ (P : Jacobian.Point W) (P' : Fin 3 → F), P.point = ⟦P'⟧ →
      (2 • P).point = ⟦dblXYZ W P'⟧ := by
    intro P P' hP
    rw [two_smul, add_point_eq P P P' P' hP hP, Jacobian.add_self]
  have add_point_of_ne : ∀ (P Q : Jacobian.Point W) (P' Q' : Fin 3 → F), P.point = ⟦P'⟧ →
      Q.point = ⟦Q'⟧ → P ≠ Q → (P + Q).point = ⟦addXYZ W P' Q'⟧ := by
    intro P Q P' Q' hP hQ ne
    rw [add_point_eq P Q P' Q' hP hQ, Jacobian.add_of_not_equiv fun h' ↦
      ne (Point.ext <| hP.trans <| (Quotient.sound h').trans hQ.symm)]
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    obtain _|_|n := n
    · rw [Nat.cast_zero, zero_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    · rw [Nat.cast_one, one_smul, smulEval, comp_fin3]; congrm(⟦?_⟧); simp [evalEval]
    obtain ⟨n, rfl|rfl⟩ := n.even_or_odd'
    · rw [add_assoc, ← two_mul, ← left_distrib, Nat.cast_mul, mul_smul, natCast_zsmul,
        two_zsmul_point _ _ (ih _ <| by omega), dblXYZ_smulEval h.1]; rfl
    · rw [show 2 * n + 1 + 1 + 1 = (n + 1) + (n + 1 + 1) by omega, Nat.cast_add, add_smul,
        add_point_of_ne _ _ _ _ (ih _ <| by omega) (ih _ <| by omega), Nat.cast_add (n + 1),
        Nat.cast_one, addXYZ_smulEval₁ h.1, ← add_assoc, two_mul]
      simp_rw [Nat.cast_add]
      rw [ne_comm, ← sub_ne_zero, ← sub_smul, add_sub_cancel_left, Nat.cast_one, one_smul]
      apply Point.fromAffine_some_ne_zero
  | neg hn n =>
    simp_rw [_root_.neg_smul, Point.neg_point, hn, eq_comm]
    refine Quotient.sound ⟨-1, ?_⟩
    simp_rw [← ringEval_comp_smulRing h.1, smulRing_neg, Jacobian.comp_smul, ← Jacobian.map_neg,
      curveRing_map_ringEval, map_neg, map_one]
    rfl

end

end WeierstrassCurve

end PortEllSequenceZSMul

section PortEllSequenceAffineBridge

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in

theorem evalEval_ψ_sq {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :
    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  have h0 : W.toAffine.polynomial.eval₂ (evalRingHom x) y = 0 := by
    rw [eval₂_evalRingHom]; exact h
  let e : W.toAffine.CoordinateRing →+* F := AdjoinRoot.lift (evalRingHom x) y h0
  have he : ∀ p : F[X][Y], e (Affine.CoordinateRing.mk W p) = p.evalEval x y := fun p ↦ by
    show AdjoinRoot.lift (evalRingHom x) y h0 (AdjoinRoot.mk _ p) = _
    rw [AdjoinRoot.lift_mk, eval₂_evalRingHom]
  calc ((W.ψ n).evalEval x y) ^ 2
      = e (Affine.CoordinateRing.mk W (W.ψ n)) ^ 2 := by rw [he]
    _ = e (Affine.CoordinateRing.mk W (W.ψ n) ^ 2) := (map_pow e _ 2).symm
    _ = e (Affine.CoordinateRing.mk W (C (W.ΨSq n))) := by
        rw [Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]
    _ = (C (W.ΨSq n)).evalEval x y := he _
    _ = (W.ΨSq n).eval x := evalEval_C x y _

omit [DecidableEq F] in

theorem evalEval_φ {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp (Affine.CoordinateRing.mk_φ W n)
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_C] at h1
  exact h1

theorem smul_eq_zero_iff_evalEval_ψ {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • (Affine.Point.some x y h) = 0 ↔ (W.ψ n).evalEval x y = 0 := by
  have key := zsmul_eq_smulEval (W := W) h n
  have hQns := (n • Jacobian.Point.fromAffine (Affine.Point.some x y h)).nonsingular
  rw [key] at hQns
  calc n • (Affine.Point.some x y h) = 0
      ↔ (Jacobian.Point.toAffineAddEquiv W).symm (n • Affine.Point.some x y h) =
        (Jacobian.Point.toAffineAddEquiv W).symm 0 := (AddEquiv.injective _).eq_iff.symm
    _ ↔ n • Jacobian.Point.fromAffine (Affine.Point.some x y h) = 0 := by
        rw [map_zsmul, map_zero, Jacobian.Point.toAffineAddEquiv_symm_apply]
    _ ↔ (⟦smulEval W x y n⟧ : Jacobian.PointClass F) = ⟦![1, 1, 0]⟧ := by
        rw [Jacobian.Point.ext_iff, key, Jacobian.Point.zero_point]
    _ ↔ (W.ψ n).evalEval x y = 0 := by
        constructor
        · intro heq
          have hz := (Jacobian.Z_eq_zero_of_equiv (Quotient.eq.mp heq)).mpr rfl
          simpa only [smulEval, Function.comp_apply, Matrix.cons_val_two, Matrix.tail_cons,
            Matrix.head_cons] using hz
        · intro hz
          refine Quotient.eq.mpr (Jacobian.equiv_zero_of_Z_eq_zero
            ((Jacobian.nonsingularLift_iff _).mp hQns) ?_)
          simpa only [smulEval, Function.comp_apply, Matrix.cons_val_two, Matrix.tail_cons,
            Matrix.head_cons] using hz

end WeierstrassCurve

end PortEllSequenceAffineBridge

namespace FunctionFieldPullback.FinrankPair

open Polynomial IntermediateField

namespace WeilPairingDEGN

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

lemma algHom_ext_of_adjoin_eq_top {L' : Type*} [Field L'] [Algebra K L'] {S : Set L}
    (hS : adjoin K S = ⊤) {f g : L →ₐ[K] L'} (h : ∀ s ∈ S, f s = g s) : f = g := by
  have hle : adjoin K S ≤ (⊤ : IntermediateField K L) := le_top
  have key : (adjoin K S).toSubfield ≤ (f : L →+* L').eqLocusField (g : L →+* L') := by
    change Subfield.closure (Set.range (algebraMap K L) ∪ S) ≤ _
    rw [Subfield.closure_le]
    rintro x (⟨k, rfl⟩ | hx)
    · simp
    · exact h x hx
  ext z
  have hz : z ∈ (adjoin K S).toSubfield := by rw [hS]; trivial
  exact key hz

lemma eq_top_of_forall_mem {B : Type*} [Field B] [Algebra K B] [Algebra B L] [IsScalarTower K B L]
    {S : Set L} (hS : adjoin K S = ⊤) (N : IntermediateField B L) (h : ∀ s ∈ S, s ∈ N) : N = ⊤ := by
  apply IntermediateField.restrictScalars_injective K
  rw [IntermediateField.restrictScalars_top, eq_top_iff, ← hS, adjoin_le_iff]
  exact h

theorem finrank_fieldRange_le (X Y : L) (hgen : adjoin K {X, Y} = ⊤) (A B : L)
    (hA : A ∈ K⟮X⟯) (hB : B ∈ K⟮X⟯) (hY : Y ^ 2 + A * Y + B = 0) (μ ι : L →ₐ[K] L)
    (hιX : ι X = X) (hιY : ι Y ^ 2 + A * ι Y + B = 0) (hιμ : ι (μ Y) ≠ μ Y) (Φ Ψ : K[X])
    {d : ℕ} (hd : 0 < d) (hroot : aeval X Φ = μ X * aeval X Ψ)
    (hdeg : ∀ (M : IntermediateField K L) (c : M),
      (Φ.map (algebraMap K M) - C c * Ψ.map (algebraMap K M)).natDegree = d) :
    FiniteDimensional μ.fieldRange L ∧ Module.finrank μ.fieldRange L ≤ d := by
  set M : IntermediateField K L := μ.fieldRange with hM
  have hxM : μ X ∈ M := ⟨X, rfl⟩
  have hyM : μ Y ∈ M := ⟨Y, rfl⟩

  set P : M[X] := Φ.map (algebraMap K M) - C (⟨μ X, hxM⟩ : M) * Ψ.map (algebraMap K M) with hP
  have hPdeg : P.natDegree = d := hdeg M _
  have hP0 : P ≠ 0 := fun h => by rw [h, natDegree_zero] at hPdeg; omega
  have hPX : aeval X P = 0 := by
    rw [hP, map_sub, map_mul, aeval_map_algebraMap, aeval_map_algebraMap, aeval_C, hroot]
    change μ X * aeval X Ψ - (algebraMap M L ⟨μ X, hxM⟩) * aeval X Ψ = 0
    rw [sub_eq_zero]; rfl
  have hXalg : IsAlgebraic M X := ⟨P, hP0, hPX⟩
  have hXint : IsIntegral M X := hXalg.isIntegral

  haveI hN'fd : FiniteDimensional M M⟮X⟯ := adjoin.finiteDimensional hXint
  have hN'deg : Module.finrank M M⟮X⟯ ≤ d := by
    rw [adjoin.finrank hXint, ← hPdeg]
    exact natDegree_le_natDegree (minpoly.degree_le_of_ne_zero M X hP0 hPX)

  have hKX : K⟮X⟯ ≤ (M⟮X⟯).restrictScalars K := by
    rw [adjoin_simple_le_iff]
    exact mem_adjoin_simple_self M X
  have hAN : A ∈ M⟮X⟯ := hKX hA
  have hBN : B ∈ M⟮X⟯ := hKX hB
  have hMN : ∀ z : L, z ∈ M → z ∈ M⟮X⟯ := fun z hz => (M⟮X⟯).algebraMap_mem ⟨z, hz⟩
  have hpair : ∀ {P : L → Prop}, P X → P Y → ∀ s ∈ ({X, Y} : Set L), P s := by
    intro P hX hY s hs
    rcases hs with h | h
    · rw [h]; exact hX
    · rw [Set.mem_singleton_iff] at h; rw [h]; exact hY
  have hXY : ∀ N : IntermediateField K L, X ∈ N → Y ∈ N → N = ⊤ := fun N hX hY =>
    eq_top_of_forall_mem hgen N (hpair hX hY)

  set N : IntermediateField K L := (M⟮X⟯).restrictScalars K with hN
  have hmemN : ∀ z, z ∈ N ↔ z ∈ M⟮X⟯ := fun z => IntermediateField.mem_restrictScalars K
  have hXN : X ∈ N := (hmemN X).mpr (mem_adjoin_simple_self M X)
  have hYN : Y ∈ N := by
    by_contra hYN

    set a : N := ⟨A, (hmemN A).mpr hAN⟩ with ha
    set b : N := ⟨B, (hmemN B).mpr hBN⟩ with hb
    set q : N[X] := Polynomial.X ^ 2 + (C a * Polynomial.X + C b) with hq
    have hlow : (C a * Polynomial.X + C b).degree < 2 := by
      refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt (degree_C_mul_X_le a) (by exact_mod_cast Nat.lt_succ_self 1)
      · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.zero_lt_two)
    have hqm : q.Monic := monic_X_pow_add hlow
    have hqdeg : q.natDegree = 2 := by
      rw [hq, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
      rwa [degree_X_pow]
    have hq0 : q ≠ 0 := hqm.ne_zero
    have haeval : ∀ z : L, aeval z q = z ^ 2 + A * z + B := by
      intro z
      rw [hq]
      simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
      rw [add_assoc]
      rfl
    have hqY : aeval Y q = 0 := by rw [haeval, hY]
    have hYint : IsIntegral N Y := ⟨q, hqm, by rwa [← aeval_def]⟩

    have hmin2 : 2 ≤ (minpoly N Y).natDegree := by
      rw [minpoly.two_le_natDegree_iff hYint]
      rintro ⟨z, hz⟩
      exact hYN (hz ▸ z.2)
    have hmin : minpoly N Y = q := by
      symm
      apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hYint) hqm
        (minpoly.dvd N Y hqY)
      rw [hqdeg]; exact hmin2

    have hιroot : ι Y ∈ (minpoly N Y).aroots L := by
      rw [mem_aroots', hmin]
      exact ⟨Polynomial.map_ne_zero hq0, by rw [haeval, hιY]⟩

    have hXNY : X ∈ N⟮Y⟯ := (N⟮Y⟯).algebraMap_mem ⟨X, hXN⟩
    have hYNY : Y ∈ N⟮Y⟯ := mem_adjoin_simple_self N Y
    have htop : N⟮Y⟯ = ⊤ := eq_top_of_forall_mem hgen _ (hpair hXNY hYNY)
    let e : L ≃ₐ[N] N⟮Y⟯ :=
      ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).symm
    let θ₀ : N⟮Y⟯ →ₐ[N] L := (algHomAdjoinIntegralEquiv N hYint).symm ⟨ι Y, hιroot⟩
    let θ : L →ₐ[N] L := θ₀.comp e
    have heY : e Y = AdjoinSimple.gen N Y := by
      apply Subtype.ext; rfl
    have hθY : θ Y = ι Y := by
      show θ₀ (e Y) = ι Y
      rw [heY]
      exact algHomAdjoinIntegralEquiv_symm_apply_gen N hYint ⟨ι Y, hιroot⟩
    have hθfix : ∀ z : L, z ∈ N → θ z = z := fun z hz => θ.commutes ⟨z, hz⟩
    have hθX : θ.restrictScalars K X = ι X := by
      rw [AlgHom.restrictScalars_apply, hθfix _ hXN, hιX]
    have hθY' : θ.restrictScalars K Y = ι Y := by
      rw [AlgHom.restrictScalars_apply, hθY]
    have hθι : θ.restrictScalars K = ι :=
      algHom_ext_of_adjoin_eq_top hgen (hpair (P := fun s => θ.restrictScalars K s = ι s) hθX hθY')
    apply hιμ
    rw [← hθι, AlgHom.restrictScalars_apply]
    exact hθfix _ ((hmemN _).mpr (hMN _ hyM))

  have htop' : M⟮X⟯ = ⊤ :=
    eq_top_of_forall_mem hgen (M⟮X⟯) (hpair (mem_adjoin_simple_self M X) ((hmemN Y).mp hYN))
  let e' : M⟮X⟯ ≃ₐ[M] L := (IntermediateField.equivOfEq htop').trans IntermediateField.topEquiv
  refine ⟨LinearEquiv.finiteDimensional e'.toLinearEquiv, ?_⟩
  rw [← LinearEquiv.finrank_eq e'.toLinearEquiv]
  exact hN'deg

end WeilPairingDEGN

theorem solution {K L : Type*} [Field K] [Field L] [Algebra K L] (X Y : L) (hgen : IntermediateField.adjoin K {X, Y} = ⊤) (A B : L) (hA : A ∈ IntermediateField.adjoin K {X}) (hB : B ∈ IntermediateField.adjoin K {X}) (hY : Y ^ 2 + A * Y + B = 0) (μ ι : L →ₐ[K] L) (hιX : ι X = X) (hιY : ι Y ^ 2 + A * ι Y + B = 0) (hιμ : ι (μ Y) ≠ μ Y) (Φ Ψ : Polynomial K) {d : ℕ} (hd : 0 < d) (hroot : Polynomial.aeval X Φ = μ X * Polynomial.aeval X Ψ) (hdeg : ∀ (M : IntermediateField K L) (c : M), (Φ.map (algebraMap K M) - Polynomial.C c * Ψ.map (algebraMap K M)).natDegree = d) : FiniteDimensional μ.fieldRange L ∧ Module.finrank μ.fieldRange L ≤ d :=
  WeilPairingDEGN.finrank_fieldRange_le X Y hgen A B hA hB hY μ ι hιX hιY hιμ Φ Ψ hd hroot hdeg
end FunctionFieldPullback.FinrankPair


theorem IntermediateField.finrank_fieldRange_le_of_adjoin_pair_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L] (X Y : L) (hgen : IntermediateField.adjoin K {X, Y} = ⊤) (A B : L) (hA : A ∈ IntermediateField.adjoin K {X}) (hB : B ∈ IntermediateField.adjoin K {X}) (hY : Y ^ 2 + A * Y + B = 0) (μ ι : L →ₐ[K] L) (hιX : ι X = X) (hιY : ι Y ^ 2 + A * ι Y + B = 0) (hιμ : ι (μ Y) ≠ μ Y) (Φ Ψ : Polynomial K) {d : ℕ} (hd : 0 < d) (hroot : Polynomial.aeval X Φ = μ X * Polynomial.aeval X Ψ) (hdeg : ∀ (M : IntermediateField K L) (c : M), (Φ.map (algebraMap K M) - Polynomial.C c * Ψ.map (algebraMap K M)).natDegree = d) : FiniteDimensional μ.fieldRange L ∧ Module.finrank μ.fieldRange L ≤ d :=
  FunctionFieldPullback.FinrankPair.solution X Y hgen A B hA hB hY μ ι hιX hιY hιμ Φ Ψ hd hroot hdeg


open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {K : Type*} [Field K] {W : Affine K}

instance moduleFinite : Module.Finite K[X] W.CoordinateRing :=
  Module.Finite.of_basis (CoordinateRing.basis W)

instance isIntegral : Algebra.IsIntegral K[X] W.CoordinateRing :=
  Algebra.IsIntegral.of_finite K[X] W.CoordinateRing

theorem algebraMap_eq_mk_C (p : K[X]) : algebraMap K[X] W.CoordinateRing p = mk W (C p) := rfl

theorem isMaximal_of_isPrime {P : Ideal W.CoordinateRing} (hP : P ≠ ⊥) [P.IsPrime] :
    P.IsMaximal := by
  have hc : (P.comap (algebraMap K[X] W.CoordinateRing)) ≠ ⊥ := fun h =>
    hP (Ideal.eq_bot_of_comap_eq_bot h)
  haveI : (P.comap (algebraMap K[X] W.CoordinateRing)).IsMaximal :=
    IsPrime.to_maximal_ideal hc
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := K[X]) P inferInstance

theorem exists_comap_eq_span [IsAlgClosed K] {P : Ideal W.CoordinateRing} (hP : P ≠ ⊥)
    [P.IsPrime] :
    ∃ a : K, P.comap (algebraMap K[X] W.CoordinateRing) = Ideal.span {X - C a} := by
  set p := P.comap (algebraMap K[X] W.CoordinateRing) with hp
  have hp0 : p ≠ ⊥ := fun h => hP (Ideal.eq_bot_of_comap_eq_bot h)
  haveI : p.IsPrime := Ideal.comap_isPrime _ P
  haveI hpmax : p.IsMaximal := IsPrime.to_maximal_ideal hp0
  set g := Submodule.IsPrincipal.generator p with hg
  have hgp : Ideal.span {g} = p := Ideal.span_singleton_generator p
  have hgprime : Prime g := Submodule.IsPrincipal.prime_generator_of_isPrime p hp0
  have hdeg : g.degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible K hgprime.irreducible
  obtain ⟨a, ha⟩ := Polynomial.exists_root_of_degree_eq_one hdeg
  refine ⟨a, ?_⟩
  have hle : p ≤ Ideal.span {X - C a} := by
    rw [← hgp, Ideal.span_singleton_le_span_singleton]
    exact ⟨g /ₘ (X - C a), (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha).symm⟩
  exact (hpmax.eq_of_le (Ideal.span_singleton_ne_top (Polynomial.not_isUnit_X_sub_C a)) hle).symm
    |>.symm

theorem XClass_mem_of_comap_eq {P : Ideal W.CoordinateRing} {a : K}
    (h : P.comap (algebraMap K[X] W.CoordinateRing) = Ideal.span {X - C a}) : XClass W a ∈ P := by
  have : X - C a ∈ P.comap (algebraMap K[X] W.CoordinateRing) := by
    rw [h]; exact Ideal.mem_span_singleton_self _
  exact this

theorem mk_C_mem_iff {P : Ideal W.CoordinateRing} {a : K}
    (h : P.comap (algebraMap K[X] W.CoordinateRing) = Ideal.span {X - C a}) (q : K[X]) :
    mk W (C q) ∈ P ↔ q.IsRoot a := by
  change q ∈ P.comap (algebraMap K[X] W.CoordinateRing) ↔ _
  rw [h, Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot]

theorem XYIdeal_isMaximal {a b : K} (h : W.Equation a b) : (XYIdeal W a (C b)).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  exact MulEquiv.isField (Field.toIsField K)
    (quotientXYIdealEquiv (W' := W) (x := a) (y := C b) h).toMulEquiv

theorem algebraMap_quot_apply (P : Ideal W.CoordinateRing) (c : K) :
    algebraMap K (W.CoordinateRing ⧸ P) c = Ideal.Quotient.mk P (mk W (C (C c))) := rfl

theorem algebraMap_quot_eq_comp_eval {P : Ideal W.CoordinateRing} {a : K}
    (h : P.comap (algebraMap K[X] W.CoordinateRing) = Ideal.span {X - C a}) :
    algebraMap K[X] (W.CoordinateRing ⧸ P) =
      (algebraMap K (W.CoordinateRing ⧸ P)).comp (evalRingHom a) := by
  apply Polynomial.ringHom_ext
  · intro c
    simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_C]
    rfl
  · simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_X]
    rw [algebraMap_quot_apply, IsScalarTower.algebraMap_apply K[X] W.CoordinateRing (W.CoordinateRing ⧸ P),
      Ideal.Quotient.algebraMap_eq, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    have : mk W (C (C a)) - algebraMap K[X] W.CoordinateRing X = -XClass W a := by
      simp only [algebraMap_eq_mk_C, XClass, map_sub]; abel
    rw [this]
    exact P.neg_mem (XClass_mem_of_comap_eq h)

theorem exists_eq_XYIdeal [IsAlgClosed K] {P : Ideal W.CoordinateRing} (hP : P ≠ ⊥) [P.IsPrime] :
    ∃ a b : K, W.Equation a b ∧ P = XYIdeal W a (C b) := by
  obtain ⟨a, ha⟩ := exists_comap_eq_span hP
  haveI hPmax : P.IsMaximal := isMaximal_of_isPrime hP
  set L := W.CoordinateRing ⧸ P
  set π := Ideal.Quotient.mk P
  have hθ := algebraMap_quot_eq_comp_eval ha

  haveI : Algebra.IsIntegral K L := ⟨fun z => by
    obtain ⟨m, hm, hm0⟩ := Algebra.IsIntegral.isIntegral (R := K[X]) z
    refine ⟨m.map (evalRingHom a), hm.map _, ?_⟩
    rw [eval₂_map, ← hθ]
    exact hm0⟩

  obtain ⟨b, hb⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := L)).2 (π (mk W Y))
  have hYmem : YClass W (C b) ∈ P := by
    rw [YClass, map_sub, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hb.symm

  have heq : W.Equation a b := by
    have hψ : π.comp (mk W) = (algebraMap K L).comp (evalEvalRingHom a b) := by
      apply Polynomial.ringHom_ext
      · intro q
        change algebraMap K[X] L q = _
        rw [hθ]
        simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_C]
        rfl
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_X, eval_C]
        exact hb.symm
    have h0 : (π.comp (mk W)) W.polynomial = 0 := by
      rw [RingHom.comp_apply, AdjoinRoot.mk_self, map_zero]
    rw [hψ, RingHom.comp_apply, coe_evalEvalRingHom, map_eq_zero] at h0
    exact h0
  refine ⟨a, b, heq, ?_⟩

  have hle : XYIdeal W a (C b) ≤ P := by
    rw [XYIdeal, Ideal.span_le]
    rintro z (rfl | rfl)
    · exact XClass_mem_of_comap_eq ha
    · exact hYmem
  exact ((XYIdeal_isMaximal heq).eq_of_le hPmax.ne_top hle).symm

end WeierstrassCurve.Affine.CoordinateRing

namespace WeierstrassCurve.Affine

namespace Point

variable {S : Type*} [CommRing S] {V : Affine S}

def xc : V.Point → S
  | 0 => 0
  | some x _ _ => x

def yc : V.Point → S
  | 0 => 0
  | some _ y _ => y

@[simp] lemma xc_some {x y : S} (h : V.Nonsingular x y) : (some x y h).xc = x := rfl
@[simp] lemma yc_some {x y : S} (h : V.Nonsingular x y) : (some x y h).yc = y := rfl

lemma nonsingular_xc_yc {P : V.Point} (hP : P ≠ 0) : V.Nonsingular P.xc P.yc := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact h

lemma eq_some_xc_yc {P : V.Point} (hP : P ≠ 0) : P = some P.xc P.yc (nonsingular_xc_yc hP) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

end Point

section Generic

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]

noncomputable instance instDecidableEqFunctionField : DecidableEq (W⁄K).FunctionField :=
  Classical.decEq _

noncomputable def genericX : (W⁄K).FunctionField :=
  algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (C X))

noncomputable def genericY : (W⁄K).FunctionField :=
  algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) Y)

theorem evalEval_baseChange_polynomial (x y : (W⁄K).FunctionField) :
    (W⁄(W⁄K).FunctionField).polynomial.evalEval x y =
      (W⁄K).polynomial.eval₂ (aeval (R := K) x).toRingHom y := by
  rw [baseChange_polynomial W (Algebra.ofId K (W⁄K).FunctionField), evalEval, eval_map]
  have h := hom_eval₂ (W⁄K).polynomial (mapRingHom (Algebra.ofId K (W⁄K).FunctionField : K →+* _))
    (evalRingHom x) (C y)
  simp only [coe_evalRingHom, eval_C] at h
  rw [h]
  congr 1
  apply Polynomial.ringHom_ext
  · intro c
    simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_C, coe_evalRingHom,
      eval_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
    rfl
  · simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, map_X, coe_evalRingHom,
      eval_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]

theorem algebraMap_comp_of :
    (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField).comp (AdjoinRoot.of (W⁄K).polynomial) =
      (aeval (R := K) (genericX W K)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro c
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      aeval_C]
    rw [← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    change (algebraMap K[X] (W⁄K).FunctionField) (algebraMap K K[X] c) = _
    exact (IsScalarTower.algebraMap_apply K K[X] (W⁄K).FunctionField c).symm
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      aeval_X]
    rfl

theorem generic_equation :
    (W⁄(W⁄K).FunctionField).Equation (genericX W K) (genericY W K) := by
  rw [Equation, evalEval_baseChange_polynomial, ← algebraMap_comp_of]
  have h0 := congrArg (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField)
    (AdjoinRoot.eval₂_root (W⁄K).polynomial)
  rw [map_zero, hom_eval₂] at h0
  exact h0

theorem generic_nonsingular [W.IsElliptic] :
    (W⁄(W⁄K).FunctionField).Nonsingular (genericX W K) (genericY W K) := by
  haveI : (W⁄(W⁄K).FunctionField).IsElliptic :=
    inferInstanceAs ((W.map (algebraMap R (W⁄K).FunctionField)).IsElliptic)
  exact (equation_iff_nonsingular (W := W⁄(W⁄K).FunctionField)).mp (generic_equation W K)

noncomputable def genericPoint [W.IsElliptic] : (W⁄(W⁄K).FunctionField).Point :=
  .some _ _ (generic_nonsingular W K)

end Generic

section PointHom

variable {R : Type*} [Field R] {W : WeierstrassCurve R} {K : Type*} [Field K] [Algebra R K]

theorem eval₂_polynomial_of_point (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) :
    (W⁄K).polynomial.eval₂ (aeval (R := K) Q.xc).toRingHom Q.yc = 0 := by
  rw [← evalEval_baseChange_polynomial]
  exact (Point.nonsingular_xc_yc hQ).left

noncomputable def pointHom (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) :
    (W⁄K).CoordinateRing →ₐ[K] (W⁄K).FunctionField :=
  { AdjoinRoot.lift (aeval (R := K) Q.xc).toRingHom Q.yc (eval₂_polynomial_of_point Q hQ) with
    commutes' := fun c => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply K (Polynomial K) (W⁄K).CoordinateRing,
        AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Polynomial.algebraMap_apply, aeval_C, Algebra.algebraMap_self, RingHom.id_apply] }

theorem pointHom_mk (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) (g : (Polynomial K)[X]) :
    pointHom Q hQ (CoordinateRing.mk (W⁄K) g) = g.eval₂ (aeval (R := K) Q.xc).toRingHom Q.yc :=
  AdjoinRoot.lift_mk (eval₂_polynomial_of_point Q hQ) g

@[simp] theorem pointHom_mk_C_C (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) (c : K) :
    pointHom Q hQ (CoordinateRing.mk (W⁄K) (C (C c))) = algebraMap K _ c :=
  (pointHom Q hQ).commutes c

@[simp] theorem pointHom_mk_C_X (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) :
    pointHom Q hQ (CoordinateRing.mk (W⁄K) (C X)) = Q.xc := by
  rw [pointHom_mk, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]

@[simp] theorem pointHom_mk_Y (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) :
    pointHom Q hQ (CoordinateRing.mk (W⁄K) Y) = Q.yc := by
  rw [pointHom_mk, eval₂_X]

theorem CoordinateRing.algHom_ext' {A : Type*} [Semiring A] [Algebra K A]
    {f g : (W⁄K).CoordinateRing →ₐ[K] A}
    (hX : f (CoordinateRing.mk (W⁄K) (C X)) = g (CoordinateRing.mk (W⁄K) (C X)))
    (hY : f (CoordinateRing.mk (W⁄K) Y) = g (CoordinateRing.mk (W⁄K) Y)) : f = g := by
  apply AlgHom.coe_ringHom_injective
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro q
    change f (CoordinateRing.mk (W⁄K) (C q)) = g (CoordinateRing.mk (W⁄K) (C q))
    have hf : (f : (W⁄K).CoordinateRing →+* A).comp ((CoordinateRing.mk (W⁄K)).comp C) =
        (g : (W⁄K).CoordinateRing →+* A).comp ((CoordinateRing.mk (W⁄K)).comp C) := by
      apply Polynomial.ringHom_ext
      · intro c
        change f (algebraMap K _ c) = g (algebraMap K _ c)
        rw [AlgHom.commutes, AlgHom.commutes]
      · exact hX
    exact RingHom.congr_fun hf q
  · exact hY

theorem pointHom_genericPoint [W.IsElliptic] :
    pointHom (genericPoint W K) (Point.some_ne_zero _) =
      IsScalarTower.toAlgHom K (W⁄K).CoordinateRing (W⁄K).FunctionField := by
  show pointHom (Point.some _ _ (generic_nonsingular W K)) _ =
      IsScalarTower.toAlgHom K (W⁄K).CoordinateRing (W⁄K).FunctionField
  apply CoordinateRing.algHom_ext'
  · rw [pointHom_mk_C_X, IsScalarTower.coe_toAlgHom', Point.xc_some]; rfl
  · rw [pointHom_mk_Y, IsScalarTower.coe_toAlgHom', Point.yc_some]; rfl

theorem Point.xc_map {F' L' : Type*} [Field F'] [Field L'] [Algebra R F'] [Algebra K F']
    [IsScalarTower R K F'] [Algebra R L'] [Algebra K L'] [IsScalarTower R K L']
    [DecidableEq F'] [DecidableEq L'] (f : F' →ₐ[K] L') (P : (W⁄F').Point) :
    (Point.map (W' := W) f P).xc = f P.xc := by
  cases P with
  | zero => exact (_root_.map_zero f).symm
  | some x y h => rfl

theorem Point.yc_map {F' L' : Type*} [Field F'] [Field L'] [Algebra R F'] [Algebra K F']
    [IsScalarTower R K F'] [Algebra R L'] [Algebra K L'] [IsScalarTower R K L']
    [DecidableEq F'] [DecidableEq L'] (f : F' →ₐ[K] L') (P : (W⁄F').Point) :
    (Point.map (W' := W) f P).yc = f P.yc := by
  cases P with
  | zero => exact (_root_.map_zero f).symm
  | some x y h => rfl

theorem pointHom_injective_of_ne_baseChange [DecidableEq K] [IsAlgClosed K] [W.IsElliptic]
    (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hQK : ∀ P : (W⁄K).Point, Q ≠ Point.baseChange K (W⁄K).FunctionField P) :
    Function.Injective (pointHom Q hQ) := by
  rw [injective_iff_map_eq_zero]
  by_contra hcon
  push Not at hcon
  have hker : RingHom.ker (pointHom Q hQ) ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := hcon
    intro h
    have hm : a ∈ RingHom.ker (pointHom Q hQ) := (RingHom.mem_ker).mpr ha
    rw [h, Ideal.mem_bot] at hm
    exact ha0 hm
  haveI : (RingHom.ker (pointHom Q hQ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨a, b, hab, hker'⟩ := CoordinateRing.exists_eq_XYIdeal hker
  haveI : (W⁄K).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  have hns : (W⁄K).Nonsingular a b := (equation_iff_nonsingular (W := W⁄K)).mp hab
  have hx : Q.xc = algebraMap K _ a := by
    have : CoordinateRing.XClass (W⁄K) a ∈ RingHom.ker (pointHom Q hQ) := by
      rw [hker']; exact Ideal.subset_span (Set.mem_insert _ _)
    rw [RingHom.mem_ker, CoordinateRing.XClass, map_sub, map_sub, map_sub, pointHom_mk_C_X,
      pointHom_mk_C_C, sub_eq_zero] at this
    exact this
  have hy : Q.yc = algebraMap K _ b := by
    have : CoordinateRing.YClass (W⁄K) (C b) ∈ RingHom.ker (pointHom Q hQ) := by
      rw [hker']; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    rw [RingHom.mem_ker, CoordinateRing.YClass, map_sub, map_sub, pointHom_mk_Y, pointHom_mk_C_C,
      sub_eq_zero] at this
    exact this
  apply hQK (.some a b hns)
  rw [Point.eq_some_xc_yc hQ, Point.baseChange, Point.map_some]
  congr 1

noncomputable def pointPull (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) :
    (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField :=
  IsFractionRing.liftAlgHom hinj

@[simp] theorem pointPull_algebraMap (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) (h : (W⁄K).CoordinateRing) :
    pointPull Q hQ hinj (algebraMap _ _ h) = pointHom Q hQ h := by
  rw [pointPull, IsFractionRing.liftAlgHom_apply]
  exact IsFractionRing.lift_algebraMap hinj h

theorem map_pointPull_genericPoint [W.IsElliptic] (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) :
    Point.map (pointPull Q hQ hinj) (genericPoint W K) = Q := by
  conv_rhs => rw [Point.eq_some_xc_yc hQ]
  rw [genericPoint, Point.map_some]
  congr 1
  · rw [genericX, pointPull_algebraMap, pointHom_mk_C_X]
  · rw [genericY, pointPull_algebraMap, pointHom_mk_Y]

theorem pointPull_comp_pointHom (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) (P : (W⁄(W⁄K).FunctionField).Point) (hP : P ≠ 0)
    (hP' : Point.map (pointPull Q hQ hinj) P ≠ 0) :
    (pointPull Q hQ hinj).comp (pointHom P hP) = pointHom (Point.map (pointPull Q hQ hinj) P) hP' := by
  apply CoordinateRing.algHom_ext'
  · rw [AlgHom.comp_apply, pointHom_mk_C_X, pointHom_mk_C_X, Point.xc_map]
  · rw [AlgHom.comp_apply, pointHom_mk_Y, pointHom_mk_Y, Point.yc_map]

theorem pointHom_congr {Q Q' : (W⁄(W⁄K).FunctionField).Point} (h : Q = Q') (hQ : Q ≠ 0) (hQ' : Q' ≠ 0) :
    pointHom Q hQ = pointHom Q' hQ' := by subst h; rfl

theorem pointPull_comp_algebraMap (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) :
    (pointPull Q hQ hinj : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
      (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField) = pointHom Q hQ :=
  RingHom.ext fun h => pointPull_algebraMap Q hQ hinj h

theorem FunctionField.algHom_ext {φ ψ : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField}
    (h : (φ : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
        (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField) =
      (ψ : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
        (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField)) : φ = ψ :=
  AlgHom.coe_ringHom_injective
    (IsLocalization.ringHom_ext (nonZeroDivisors (W⁄K).CoordinateRing) h)

theorem exists_eq_baseChange_of_isIntegral_xc [DecidableEq K] [IsAlgClosed K] [W.IsElliptic]
    (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) (hx : _root_.IsIntegral K Q.xc) :
    ∃ P : (W⁄K).Point, Q = Point.baseChange K (W⁄K).FunctionField P := by
  haveI : (W⁄K).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance

  have hdx : (minpoly K Q.xc).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hx)
  obtain ⟨a, ha⟩ : Q.xc ∈ (algebraMap K (W⁄K).FunctionField).range := minpoly.mem_range_of_degree_eq_one K _ hdx

  have heq := (Point.nonsingular_xc_yc hQ).left
  rw [equation_iff] at heq
  have hy : _root_.IsIntegral K Q.yc := by
    refine ⟨X ^ 2 + C ((W⁄K).a₁ * a + (W⁄K).a₃) * X - C (a ^ 3 + (W⁄K).a₂ * a ^ 2 + (W⁄K).a₄ * a + (W⁄K).a₆),
      ?_, ?_⟩
    · have hlt : (C ((W⁄K).a₁ * a + (W⁄K).a₃) * X -
          C (a ^ 3 + (W⁄K).a₂ * a ^ 2 + (W⁄K).a₄ * a + (W⁄K).a₆) : K[X]).degree < ((X : K[X]) ^ 2).degree := by
        rw [degree_X_pow]
        refine (degree_sub_le _ _).trans_lt (max_lt ((degree_C_mul_X_le _).trans_lt ?_)
          (degree_C_le.trans_lt ?_))
        · exact WithBot.coe_lt_coe.mpr (by norm_num)
        · exact WithBot.coe_lt_coe.mpr (by norm_num)
      rw [add_sub_assoc]
      exact (monic_X_pow 2).add_of_left hlt
    · simp only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, map_add, map_mul, map_pow]
      rw [ha]
      have e1 : (algebraMap K (W⁄K).FunctionField) (W⁄K).a₁ = (W⁄(W⁄K).FunctionField).a₁ :=
        (IsScalarTower.algebraMap_apply R K (W⁄K).FunctionField W.a₁).symm
      have e2 : (algebraMap K (W⁄K).FunctionField) (W⁄K).a₂ = (W⁄(W⁄K).FunctionField).a₂ :=
        (IsScalarTower.algebraMap_apply R K (W⁄K).FunctionField W.a₂).symm
      have e3 : (algebraMap K (W⁄K).FunctionField) (W⁄K).a₃ = (W⁄(W⁄K).FunctionField).a₃ :=
        (IsScalarTower.algebraMap_apply R K (W⁄K).FunctionField W.a₃).symm
      have e4 : (algebraMap K (W⁄K).FunctionField) (W⁄K).a₄ = (W⁄(W⁄K).FunctionField).a₄ :=
        (IsScalarTower.algebraMap_apply R K (W⁄K).FunctionField W.a₄).symm
      have e6 : (algebraMap K (W⁄K).FunctionField) (W⁄K).a₆ = (W⁄(W⁄K).FunctionField).a₆ :=
        (IsScalarTower.algebraMap_apply R K (W⁄K).FunctionField W.a₆).symm
      rw [e1, e2, e3, e4, e6]
      linear_combination heq
  have hdy : (minpoly K Q.yc).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hy)
  obtain ⟨b, hb⟩ : Q.yc ∈ (algebraMap K (W⁄K).FunctionField).range := minpoly.mem_range_of_degree_eq_one K _ hdy
  have hab : (W⁄K).Equation a b := by
    rw [← baseChange_equation W (Algebra.ofId K (W⁄K).FunctionField).injective a b]
    change (W⁄(W⁄K).FunctionField).Equation (algebraMap K _ a) (algebraMap K _ b)
    rw [ha, hb]
    exact (Point.nonsingular_xc_yc hQ).left
  have hns : (W⁄K).Nonsingular a b := (equation_iff_nonsingular (W := W⁄K)).mp hab
  refine ⟨.some a b hns, ?_⟩
  rw [Point.eq_some_xc_yc hQ, Point.baseChange, Point.map_some]
  congr 1 <;> [exact ha.symm; exact hb.symm]

theorem not_isIntegral_xc_of_ne_baseChange [DecidableEq K] [IsAlgClosed K] [W.IsElliptic]
    (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hQK : ∀ P : (W⁄K).Point, Q ≠ Point.baseChange K (W⁄K).FunctionField P) :
    ¬ _root_.IsIntegral K Q.xc :=
  fun hx => by obtain ⟨P, hP⟩ := exists_eq_baseChange_of_isIntegral_xc Q hQ hx; exact hQK P hP

end PointHom

section TransMul

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K] [IsAlgClosed K] [W.IsElliptic]

omit [IsAlgClosed K] in

theorem genericPoint_ne_baseChange (P : (W⁄K).Point) :
    genericPoint W K ≠ Point.baseChange K (W⁄K).FunctionField P := by
  intro h
  cases P with
  | zero => exact Point.some_ne_zero _ (h.trans (map_zero _))
  | some a b hab =>
    rw [genericPoint, Point.baseChange, Point.map_some, Point.some.injEq] at h
    apply CoordinateRing.XClass_ne_zero (W' := W⁄K) a
    apply IsFractionRing.injective (W⁄K).CoordinateRing (W⁄K).FunctionField
    rw [CoordinateRing.XClass, map_sub, map_sub, map_sub, _root_.map_zero]
    have h1 : algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (C X)) =
        genericX W K := rfl
    have h2 : algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) (C (C a))) =
        algebraMap K (W⁄K).FunctionField a :=
      (IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField a).symm
    rw [h1, h2, h.1, sub_eq_zero]
    rfl

omit [IsAlgClosed K] in

theorem genericPoint_add_baseChange_ne_zero (S : (W⁄K).Point) :
    genericPoint W K + Point.baseChange K _ S ≠ 0 := by
  intro h
  apply genericPoint_ne_baseChange W K (-S)
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_left h

omit [IsAlgClosed K] in

theorem genericPoint_add_baseChange_ne_baseChange (S P : (W⁄K).Point) :
    genericPoint W K + Point.baseChange K _ S ≠ Point.baseChange K _ P := by
  intro h
  apply genericPoint_ne_baseChange W K (P - S)
  rw [map_sub, ← h, add_sub_cancel_right]

theorem transHom_injective (S : (W⁄K).Point) :
    Function.Injective (pointHom (genericPoint W K + Point.baseChange K _ S)
      (genericPoint_add_baseChange_ne_zero W K S)) :=
  pointHom_injective_of_ne_baseChange _ _ (genericPoint_add_baseChange_ne_baseChange W K S)

noncomputable def transPull (S : (W⁄K).Point) : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField :=
  pointPull _ (genericPoint_add_baseChange_ne_zero W K S) (transHom_injective W K S)

theorem map_transPull_genericPoint (S : (W⁄K).Point) :
    Point.map (transPull W K S) (genericPoint W K) = genericPoint W K + Point.baseChange K _ S :=
  map_pointPull_genericPoint _ _ _

theorem map_transPull_genericPoint_add (S T : (W⁄K).Point) :
    Point.map (transPull W K S) (genericPoint W K + Point.baseChange K _ T) =
      genericPoint W K + Point.baseChange K _ (S + T) := by
  rw [map_add, map_transPull_genericPoint, Point.map_baseChange, add_assoc, ← map_add]

theorem transPull_comp_algebraMap (S : (W⁄K).Point) :
    (transPull W K S : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
      (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField) =
      pointHom (genericPoint W K + Point.baseChange K _ S) (genericPoint_add_baseChange_ne_zero W K S) :=
  pointPull_comp_algebraMap _ (genericPoint_add_baseChange_ne_zero W K S) (transHom_injective W K S)

theorem transPull_comp_pointHom (S : (W⁄K).Point) (P : (W⁄(W⁄K).FunctionField).Point) (hP : P ≠ 0)
    (hP' : Point.map (transPull W K S) P ≠ 0) :
    (transPull W K S).comp (pointHom P hP) = pointHom (Point.map (transPull W K S) P) hP' :=
  pointPull_comp_pointHom _ _ _ P hP hP'

theorem transPull_comp_transHom (S T : (W⁄K).Point) :
    (transPull W K S).comp (pointHom (genericPoint W K + Point.baseChange K _ T)
      (genericPoint_add_baseChange_ne_zero W K T)) =
      pointHom (genericPoint W K + Point.baseChange K _ (S + T))
        (genericPoint_add_baseChange_ne_zero W K (S + T)) := by
  apply CoordinateRing.algHom_ext'
  · rw [AlgHom.comp_apply, pointHom_mk_C_X, pointHom_mk_C_X, ← map_transPull_genericPoint_add,
      Point.xc_map]
  · rw [AlgHom.comp_apply, pointHom_mk_Y, pointHom_mk_Y, ← map_transPull_genericPoint_add,
      Point.yc_map]

theorem transPull_comp (S T : (W⁄K).Point) :
    (transPull W K S).comp (transPull W K T) = transPull W K (S + T) := by
  apply FunctionField.algHom_ext
  rw [AlgHom.comp_toRingHom, RingHom.comp_assoc, transPull_comp_algebraMap W K T,
    transPull_comp_algebraMap W K (S + T), ← AlgHom.comp_toRingHom, transPull_comp_transHom]

theorem transPull_zero : transPull W K 0 = AlgHom.id K _ := by
  apply FunctionField.algHom_ext
  rw [transPull_comp_algebraMap]
  have h0 : genericPoint W K + Point.baseChange K (W⁄K).FunctionField (0 : (W⁄K).Point) =
      genericPoint W K := by
    rw [map_zero, add_zero]
  rw [pointHom_congr h0 _ (Point.some_ne_zero _), pointHom_genericPoint]
  exact RingHom.ext fun x => rfl

noncomputable def transEquiv (S : (W⁄K).Point) : (W⁄K).FunctionField ≃ₐ[K] (W⁄K).FunctionField :=
  AlgEquiv.ofAlgHom (transPull W K S) (transPull W K (-S))
    (by rw [transPull_comp, add_neg_cancel, transPull_zero])
    (by rw [transPull_comp, neg_add_cancel, transPull_zero])

theorem transEquiv_apply (S : (W⁄K).Point) (h : (W⁄K).FunctionField) :
    transEquiv W K S h = transPull W K S h := rfl

theorem coe_transEquiv (S : (W⁄K).Point) :
    (transEquiv W K S : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField) = transPull W K S := rfl

theorem transEquiv_algebraMap (S : (W⁄K).Point) (h : (W⁄K).CoordinateRing) :
    transEquiv W K S (algebraMap _ _ h) =
      pointHom (genericPoint W K + Point.baseChange K _ S) (genericPoint_add_baseChange_ne_zero W K S) h :=
  pointPull_algebraMap _ (genericPoint_add_baseChange_ne_zero W K S) (transHom_injective W K S) h

theorem transEquiv_genericX (S : (W⁄K).Point) :
    transEquiv W K S (genericX W K) = (genericPoint W K + Point.baseChange K _ S).xc := by
  rw [genericX, transEquiv_algebraMap, pointHom_mk_C_X]

theorem transEquiv_genericY (S : (W⁄K).Point) :
    transEquiv W K S (genericY W K) = (genericPoint W K + Point.baseChange K _ S).yc := by
  rw [genericY, transEquiv_algebraMap, pointHom_mk_Y]

theorem map_transEquiv_genericPoint (S : (W⁄K).Point) :
    Point.map (transEquiv W K S : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField) (genericPoint W K) =
      genericPoint W K + Point.baseChange K _ S := by
  rw [coe_transEquiv, map_transPull_genericPoint]

theorem transEquiv_add (S T : (W⁄K).Point) :
    transEquiv W K (S + T) = (transEquiv W K T).trans (transEquiv W K S) := by
  apply AlgEquiv.ext
  intro h
  rw [AlgEquiv.trans_apply, transEquiv_apply, transEquiv_apply, transEquiv_apply,
    ← AlgHom.comp_apply, transPull_comp]

theorem transEquiv_zero : transEquiv W K 0 = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro h
  rw [transEquiv_apply, transPull_zero]
  rfl

theorem transEquiv_injective : Function.Injective (transEquiv W K) := by
  intro S T h
  have hx := transEquiv_genericX W K S
  have hy := transEquiv_genericY W K S
  rw [h, transEquiv_genericX] at hx
  rw [h, transEquiv_genericY] at hy
  have hpt : genericPoint W K + Point.baseChange K _ T = genericPoint W K + Point.baseChange K _ S := by
    rw [Point.eq_some_xc_yc (genericPoint_add_baseChange_ne_zero W K T),
      Point.eq_some_xc_yc (genericPoint_add_baseChange_ne_zero W K S)]
    congr 1
  exact (Point.map_injective _ (add_left_cancel hpt)).symm

omit [IsAlgClosed K] in
theorem neg_genericPoint_ne_baseChange (P : (W⁄K).Point) :
    -genericPoint W K ≠ Point.baseChange K (W⁄K).FunctionField P := by
  intro h
  apply genericPoint_ne_baseChange W K (-P)
  rw [map_neg, ← h, neg_neg]

theorem negHom_injective :
    Function.Injective (pointHom (-genericPoint W K) (neg_ne_zero.mpr (Point.some_ne_zero _))) :=
  pointHom_injective_of_ne_baseChange _ _ (neg_genericPoint_ne_baseChange W K)

noncomputable def negPull : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField :=
  pointPull _ (neg_ne_zero.mpr (Point.some_ne_zero _)) (negHom_injective W K)

theorem map_negPull_genericPoint : Point.map (negPull W K) (genericPoint W K) = -genericPoint W K :=
  map_pointPull_genericPoint _ _ _

theorem negPull_algebraMap (g : (W⁄K).CoordinateRing) :
    negPull W K (algebraMap _ _ g) = pointHom (-genericPoint W K) (neg_ne_zero.mpr (Point.some_ne_zero _)) g :=
  pointPull_algebraMap _ _ _ g

theorem negPull_comp_algebraMap :
    (negPull W K : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
      (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField) =
      pointHom (-genericPoint W K) (neg_ne_zero.mpr (Point.some_ne_zero _)) :=
  pointPull_comp_algebraMap _ _ _

theorem negPull_comp_pointHom (P : (W⁄(W⁄K).FunctionField).Point) (hP : P ≠ 0)
    (hP' : Point.map (negPull W K) P ≠ 0) :
    (negPull W K).comp (pointHom P hP) = pointHom (Point.map (negPull W K) P) hP' :=
  pointPull_comp_pointHom _ _ _ P hP hP'

theorem negPull_comp_negPull : (negPull W K).comp (negPull W K) = AlgHom.id K _ := by
  apply FunctionField.algHom_ext
  have hP' : Point.map (negPull W K) (-genericPoint W K) = genericPoint W K := by
    rw [map_neg, map_negPull_genericPoint, neg_neg]
  rw [AlgHom.comp_toRingHom, RingHom.comp_assoc, negPull_comp_algebraMap, ← AlgHom.comp_toRingHom,
    negPull_comp_pointHom W K _ _ (by rw [hP']; exact Point.some_ne_zero _),
    pointHom_congr hP' _ (Point.some_ne_zero _), pointHom_genericPoint]
  exact RingHom.ext fun x => rfl

noncomputable def negEquiv : (W⁄K).FunctionField ≃ₐ[K] (W⁄K).FunctionField :=
  AlgEquiv.ofAlgHom (negPull W K) (negPull W K) (negPull_comp_negPull W K) (negPull_comp_negPull W K)

theorem coe_negEquiv : (negEquiv W K : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField) = negPull W K := rfl

theorem negEquiv_apply (h : (W⁄K).FunctionField) : negEquiv W K h = negPull W K h := rfl

theorem map_negEquiv_genericPoint :
    Point.map (negEquiv W K : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField) (genericPoint W K) =
      -genericPoint W K := by
  rw [coe_negEquiv, map_negPull_genericPoint]

theorem negEquiv_genericX : negEquiv W K (genericX W K) = genericX W K := by
  rw [negEquiv_apply, genericX, negPull_algebraMap, pointHom_mk_C_X]
  simp only [genericPoint, Point.neg_some, Point.xc_some]
  rfl

theorem negEquiv_genericY :
    negEquiv W K (genericY W K) = (W⁄(W⁄K).FunctionField).negY (genericX W K) (genericY W K) := by
  rw [negEquiv_apply, genericY, negPull_algebraMap, pointHom_mk_Y]
  simp only [genericPoint, Point.neg_some, Point.yc_some]
  rfl

theorem negEquiv_symm : (negEquiv W K).symm = negEquiv W K := rfl

def MulGood (n : ℤ) : Prop :=
  n • genericPoint W K ≠ 0 ∧
    ∀ P : (W⁄K).Point, n • genericPoint W K ≠ Point.baseChange K (W⁄K).FunctionField P

theorem mulHom_injective {n : ℤ} (h : MulGood W K n) :
    Function.Injective (pointHom (n • genericPoint W K) h.1) :=
  pointHom_injective_of_ne_baseChange _ _ h.2

noncomputable def mulPull (n : ℤ) (h : MulGood W K n) :
    (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField :=
  pointPull (n • genericPoint W K) h.1 (mulHom_injective W K h)

theorem mulPull_eq {n : ℤ} (h : MulGood W K n) :
    mulPull W K n h = pointPull (n • genericPoint W K) h.1 (mulHom_injective W K h) := rfl

theorem mulPull_algebraMap {n : ℤ} (h : MulGood W K n) (g : (W⁄K).CoordinateRing) :
    mulPull W K n h (algebraMap _ _ g) = pointHom (n • genericPoint W K) h.1 g := by
  rw [mulPull_eq W K h, pointPull_algebraMap]

theorem mulPull_comp_algebraMap {n : ℤ} (h : MulGood W K n) :
    (mulPull W K n h : (W⁄K).FunctionField →+* (W⁄K).FunctionField).comp
      (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField) = pointHom (n • genericPoint W K) h.1 :=
  RingHom.ext fun g => mulPull_algebraMap W K h g

theorem mulPull_genericX' {n : ℤ} (h : MulGood W K n) :
    mulPull W K n h (genericX W K) = (n • genericPoint W K).xc := by
  rw [genericX, mulPull_algebraMap W K h, pointHom_mk_C_X]

theorem mulPull_genericY' {n : ℤ} (h : MulGood W K n) :
    mulPull W K n h (genericY W K) = (n • genericPoint W K).yc := by
  rw [genericY, mulPull_algebraMap W K h, pointHom_mk_Y]

theorem map_mulPull_genericPoint' {n : ℤ} (h : MulGood W K n) :
    Point.map (mulPull W K n h) (genericPoint W K) = n • genericPoint W K := by
  rw [mulPull_eq W K h, map_pointPull_genericPoint]

theorem mulPull_comp_pointHom {n : ℤ} (h : MulGood W K n) (P : (W⁄(W⁄K).FunctionField).Point)
    (hP : P ≠ 0) (hP' : Point.map (mulPull W K n h) P ≠ 0) :
    (mulPull W K n h).comp (pointHom P hP) = pointHom (Point.map (mulPull W K n h) P) hP' := by
  have hP'' : Point.map (pointPull (n • genericPoint W K) h.1 (mulHom_injective W K h)) P ≠ 0 := by
    rw [← mulPull_eq W K h]; exact hP'
  rw [pointHom_congr (congrArg (fun φ => Point.map φ P) (mulPull_eq W K h)) hP' hP'', mulPull_eq W K h]
  exact pointPull_comp_pointHom _ _ _ P hP hP''

theorem transEquiv_mulPull' {n : ℤ} (h : MulGood W K n) {S : (W⁄K).Point} (hS : n • S = 0)
    (g : (W⁄K).FunctionField) : transEquiv W K S (mulPull W K n h g) = mulPull W K n h g := by
  rw [transEquiv_apply, ← AlgHom.comp_apply]
  congr 1
  apply FunctionField.algHom_ext
  have hP' : Point.map (transPull W K S) (n • genericPoint W K) = n • genericPoint W K := by
    rw [map_zsmul, map_transPull_genericPoint, smul_add, ← map_zsmul, hS, map_zero, add_zero]
  rw [AlgHom.comp_toRingHom, RingHom.comp_assoc, mulPull_comp_algebraMap W K h, ← AlgHom.comp_toRingHom,
    transPull_comp_pointHom W K S _ _ (by rw [hP']; exact h.1)]
  exact congrArg _ (pointHom_congr hP' _ _)

theorem mulPull_comp' {m n : ℤ} (hm : MulGood W K m) (hn : MulGood W K n) (hnm : MulGood W K (n * m)) :
    (mulPull W K m hm).comp (mulPull W K n hn) = mulPull W K (n * m) hnm := by
  apply FunctionField.algHom_ext
  have hP' : Point.map (mulPull W K m hm) (n • genericPoint W K) = (n * m) • genericPoint W K := by
    rw [map_zsmul, map_mulPull_genericPoint' W K hm, smul_smul]
  rw [AlgHom.comp_toRingHom, RingHom.comp_assoc, mulPull_comp_algebraMap W K hn,
    mulPull_comp_algebraMap W K hnm, ← AlgHom.comp_toRingHom,
    mulPull_comp_pointHom W K hm _ _ (by rw [hP']; exact hnm.1)]
  exact congrArg _ (pointHom_congr hP' _ _)

omit [DecidableEq K] in

theorem exists_point_xc_eq (x : K) : ∃ P : (W⁄K).Point, P ≠ 0 ∧ P.xc = x := by
  haveI : (W⁄K).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  set c := (W⁄K).a₁ * x + (W⁄K).a₃ with hc
  set d := -(x ^ 3 + (W⁄K).a₂ * x ^ 2 + (W⁄K).a₄ * x + (W⁄K).a₆) with hd
  have hlt : (C c * X + C d : K[X]).degree < ((X : K[X]) ^ 2).degree := by
    rw [degree_X_pow]
    refine (degree_add_le _ _).trans_lt (max_lt ((degree_C_mul_X_le c).trans_lt ?_)
      (degree_C_le.trans_lt ?_))
    · exact WithBot.coe_lt_coe.mpr (by norm_num)
    · exact WithBot.coe_lt_coe.mpr (by norm_num)
  have hdeg : ((X : K[X]) ^ 2 + (C c * X + C d)).degree = 2 := by
    rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]; rfl
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root ((X : K[X]) ^ 2 + (C c * X + C d))
    (by rw [hdeg]; exact two_ne_zero)
  have hroot : y ^ 2 + (c * y + d) = 0 := by
    have := hy.eq_zero
    simpa only [eval_add, eval_pow, eval_X, eval_mul, eval_C] using this
  have heq : (W⁄K).Equation x y := by
    rw [equation_iff]
    rw [hc, hd] at hroot
    linear_combination hroot
  exact ⟨.some x y ((equation_iff_nonsingular (W := W⁄K)).mp heq), Point.some_ne_zero _, rfl⟩

omit [DecidableEq K] in
theorem infinite_point : Infinite (W⁄K).Point := by
  choose f hf0 hfx using exists_point_xc_eq W K
  exact Infinite.of_injective f fun x y h => by rw [← hfx x, ← hfx y, h]

theorem map_negEquiv_zsmul_genericPoint (n : ℤ) :
    Point.map (negEquiv W K : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField) (n • genericPoint W K) =
      -(n • genericPoint W K) := by
  rw [map_zsmul, map_negEquiv_genericPoint, smul_neg]

theorem negEquiv_mulPull_genericX' {n : ℤ} (h : MulGood W K n) :
    negEquiv W K (mulPull W K n h (genericX W K)) = (n • genericPoint W K).xc := by
  rw [mulPull_genericX' W K h, ← AlgEquiv.coe_algHom, ← Point.xc_map (W := W) (K := K),
    map_negEquiv_zsmul_genericPoint, Point.eq_some_xc_yc h.1, Point.neg_some, Point.xc_some, Point.xc_some]

theorem negEquiv_mulPull_genericY' {n : ℤ} (h : MulGood W K n) :
    negEquiv W K (mulPull W K n h (genericY W K)) =
      (W⁄(W⁄K).FunctionField).negY (n • genericPoint W K).xc (n • genericPoint W K).yc := by
  rw [mulPull_genericY' W K h, ← AlgEquiv.coe_algHom, ← Point.yc_map (W := W) (K := K),
    map_negEquiv_zsmul_genericPoint]
  conv_lhs => rw [Point.eq_some_xc_yc h.1, Point.neg_some, Point.yc_some]

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
theorem mulPull_injective [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] {n : ℤ}
    (h : MulGood W K n) : Function.Injective (mulPull W K n h) := (mulPull W K n h).injective

end TransMul

section Places

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K]

noncomputable def placeOf (P : (W⁄K).Point) (hP : P ≠ 0) :
    IsDedekindDomain.HeightOneSpectrum (W⁄K).CoordinateRing where
  asIdeal := CoordinateRing.XYIdeal (W⁄K) P.xc (C P.yc)
  isPrime := (CoordinateRing.XYIdeal_isMaximal (Point.nonsingular_xc_yc hP).left).isPrime
  ne_bot h := CoordinateRing.XClass_ne_zero (W' := W⁄K) P.xc
    (by rw [← Ideal.mem_bot, ← h]; exact Ideal.subset_span (Set.mem_insert _ _))

omit [DecidableEq K] in
@[simp] theorem placeOf_asIdeal (P : (W⁄K).Point) (hP : P ≠ 0) :
    (placeOf W K P hP).asIdeal = CoordinateRing.XYIdeal (W⁄K) P.xc (C P.yc) := rfl

omit [DecidableEq K] in

theorem placeOf_surjective [IsAlgClosed K] [W.IsElliptic]
    (v : IsDedekindDomain.HeightOneSpectrum (W⁄K).CoordinateRing) :
    ∃ (P : (W⁄K).Point) (hP : P ≠ 0), placeOf W K P hP = v := by
  haveI : (W⁄K).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  haveI := v.isPrime
  obtain ⟨a, b, hab, hv⟩ := CoordinateRing.exists_eq_XYIdeal v.ne_bot
  refine ⟨.some a b ((equation_iff_nonsingular (W := W⁄K)).mp hab), Point.some_ne_zero _, ?_⟩
  exact IsDedekindDomain.HeightOneSpectrum.ext hv.symm

noncomputable def CoordinateRing.evalAt {a b : K} (h : (W⁄K).Equation a b) : (W⁄K).CoordinateRing →+* K :=
  AdjoinRoot.evalEval h

omit [DecidableEq K] in
theorem CoordinateRing.evalAt_mk {a b : K} (h : (W⁄K).Equation a b) (g : K[X][Y]) :
    CoordinateRing.evalAt W K h (CoordinateRing.mk (W⁄K) g) = g.evalEval a b :=
  AdjoinRoot.evalEval_mk h g

omit [DecidableEq K] in
theorem CoordinateRing.evalAt_XYIdeal {a b : K} (h : (W⁄K).Equation a b) :
    ∀ g ∈ CoordinateRing.XYIdeal (W⁄K) a (C b), CoordinateRing.evalAt W K h g = 0 := by
  intro g hg
  rw [← RingHom.mem_ker]
  revert hg g
  rw [← SetLike.le_def, CoordinateRing.XYIdeal, Ideal.span_le]
  rintro g (rfl | rfl)
  · rw [SetLike.mem_coe, RingHom.mem_ker, CoordinateRing.XClass, CoordinateRing.evalAt_mk,
      evalEval_C, eval_sub, eval_X, eval_C, sub_self]
  · rw [SetLike.mem_coe, RingHom.mem_ker, CoordinateRing.YClass, CoordinateRing.evalAt_mk,
      evalEval_sub, evalEval_X, evalEval_C, eval_C, sub_self]

omit [DecidableEq K] in
theorem placeOf_injective {P Q : (W⁄K).Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : placeOf W K P hP = placeOf W K Q hQ) : P = Q := by
  have hI : CoordinateRing.XYIdeal (W⁄K) P.xc (C P.yc) = CoordinateRing.XYIdeal (W⁄K) Q.xc (C Q.yc) :=
    congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h
  have hev := CoordinateRing.evalAt_XYIdeal W K (Point.nonsingular_xc_yc hP).left
  rw [hI] at hev
  have hx : P.xc = Q.xc := by
    have := hev _ (Ideal.subset_span (Set.mem_insert _ _))
    rw [CoordinateRing.XClass, CoordinateRing.evalAt_mk, evalEval_C, eval_sub, eval_X, eval_C,
      sub_eq_zero] at this
    exact this
  have hy : P.yc = Q.yc := by
    have := hev _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    rw [CoordinateRing.YClass, CoordinateRing.evalAt_mk, evalEval_sub, evalEval_X, evalEval_C, eval_C,
      sub_eq_zero] at this
    exact this
  rw [Point.eq_some_xc_yc hP, Point.eq_some_xc_yc hQ]
  congr 1

end Places

end WeierstrassCurve.Affine

open Polynomial

namespace Valuation

variable {L : Type*} [CommRing L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)

def Cong (a b : L) : Prop := v (a - b) < 1

variable {v}

theorem cong_iff {a b : L} : v.Cong a b ↔ v (a - b) < 1 := Iff.rfl

@[refl] theorem Cong.refl (a : L) : v.Cong a a := by simp [Cong]

theorem Cong.rfl {a : L} : v.Cong a a := Cong.refl a

@[symm] theorem Cong.symm {a b : L} (h : v.Cong a b) : v.Cong b a := by
  rw [Cong, ← Valuation.map_neg, neg_sub]; exact h

theorem Cong.trans {a b c : L} (h₁ : v.Cong a b) (h₂ : v.Cong b c) : v.Cong a c := by
  have : a - c = (a - b) + (b - c) := by ring
  rw [Cong, this]
  exact (v.map_add _ _).trans_lt (max_lt h₁ h₂)

theorem Cong.add {a b a' b' : L} (h₁ : v.Cong a a') (h₂ : v.Cong b b') : v.Cong (a + b) (a' + b') := by
  have : a + b - (a' + b') = (a - a') + (b - b') := by ring
  rw [Cong, this]
  exact (v.map_add _ _).trans_lt (max_lt h₁ h₂)

theorem Cong.neg {a a' : L} (h : v.Cong a a') : v.Cong (-a) (-a') := by
  have : -a - -a' = -(a - a') := by ring
  rw [Cong, this, Valuation.map_neg]; exact h

theorem Cong.sub {a b a' b' : L} (h₁ : v.Cong a a') (h₂ : v.Cong b b') : v.Cong (a - b) (a' - b') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact h₁.add h₂.neg

theorem Cong.le_one {a a' : L} (h : v.Cong a a') (ha' : v a' ≤ 1) : v a ≤ 1 := by
  have : a = (a - a') + a' := by ring
  rw [this]
  exact (v.map_add _ _).trans (max_le h.le ha')

theorem Cong.mul {a b a' b' : L} (h₁ : v.Cong a a') (h₂ : v.Cong b b') (ha' : v a' ≤ 1)
    (hb' : v b' ≤ 1) : v.Cong (a * b) (a' * b') := by
  have ha : v a ≤ 1 := h₁.le_one ha'
  have : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
  rw [Cong, this]
  refine (v.map_add _ _).trans_lt (max_lt ?_ ?_)
  · rw [Valuation.map_mul]
    calc v a * v (b - b') ≤ 1 * v (b - b') := mul_le_mul' ha le_rfl
      _ < 1 := by rw [one_mul]; exact h₂
  · rw [Valuation.map_mul]
    calc v (a - a') * v b' ≤ v (a - a') * 1 := mul_le_mul' le_rfl hb'
      _ < 1 := by rw [mul_one]; exact h₁

theorem Cong.pow {a a' : L} (h : v.Cong a a') (ha' : v a' ≤ 1) (n : ℕ) : v.Cong (a ^ n) (a' ^ n) := by
  induction n with
  | zero => simp only [pow_zero]; exact Cong.rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h (by rw [Valuation.map_pow]; exact pow_le_one' ha' n) ha'

theorem Cong.eq_of_eq_one {a a' : L} (h : v.Cong a a') (ha' : v a' = 1) : v a = 1 := by
  have : a = a' + (a - a') := by ring
  rw [this, Valuation.map_add_eq_of_lt_left]
  · exact ha'
  · rw [ha']; exact h

theorem Cong.lt_one_iff {a a' : L} (h : v.Cong a a') : v a < 1 ↔ v a' < 1 := by
  constructor
  · intro ha
    have : a' = a - (a - a') := by ring
    rw [this]
    exact (v.map_sub _ _).trans_lt (max_lt ha h)
  · intro ha'
    have : a = (a - a') + a' := by ring
    rw [this]
    exact (v.map_add _ _).trans_lt (max_lt h ha')

theorem cong_zero_iff {a : L} : v.Cong a 0 ↔ v a < 1 := by rw [Cong, sub_zero]

section Field

variable {F : Type*} [Field F] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}

theorem Cong.inv {d d' : F} (h : w.Cong d d') (hd' : w d' = 1) : w.Cong d⁻¹ d'⁻¹ := by
  have hd : w d = 1 := h.eq_of_eq_one hd'
  have hd0 : d ≠ 0 := fun h0 => by rw [h0, Valuation.map_zero] at hd; exact zero_ne_one hd
  have hd0' : d' ≠ 0 := fun h0 => by rw [h0, Valuation.map_zero] at hd'; exact zero_ne_one hd'
  have : d⁻¹ - d'⁻¹ = -(d - d') * (d⁻¹ * d'⁻¹) := by
    field_simp
    ring
  rw [Cong, this, Valuation.map_mul, Valuation.map_neg, Valuation.map_mul, map_inv₀, map_inv₀, hd, hd',
    inv_one, mul_one, mul_one]
  exact h

theorem Cong.div {a d a' d' : F} (h₁ : w.Cong a a') (h₂ : w.Cong d d') (ha' : w a' ≤ 1)
    (hd' : w d' = 1) : w.Cong (a / d) (a' / d') := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact h₁.mul (h₂.inv hd') ha' (by rw [map_inv₀, hd', inv_one])

end Field

section Eval

variable {K : Type*} [CommRing K] (f : K →+* L)

theorem Cong.eval₂ (hf : ∀ c, v (f c) ≤ 1) {a a' : L} (h : v.Cong a a') (ha' : v a' ≤ 1) (p : K[X]) :
    v.Cong (p.eval₂ f a) (p.eval₂ f a') ∧ v (p.eval₂ f a') ≤ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [eval₂_add, eval₂_add]
    exact ⟨hp.1.add hq.1, (v.map_add _ _).trans (max_le hp.2 hq.2)⟩
  | monomial n c =>
    rw [eval₂_monomial, eval₂_monomial]
    have hpow : v (a' ^ n) ≤ 1 := by rw [Valuation.map_pow]; exact pow_le_one' ha' n
    exact ⟨(Cong.refl (f c)).mul (h.pow ha' n) (hf c) hpow,
      by rw [Valuation.map_mul]; exact mul_le_one' (hf c) hpow⟩

theorem Cong.eval₂_eval₂ (hf : ∀ c, v (f c) ≤ 1) {a a' b b' : L} (ha : v.Cong a a') (ha' : v a' ≤ 1)
    (hb : v.Cong b b') (hb' : v b' ≤ 1) (p : K[X][X]) :
    v.Cong (p.eval₂ (eval₂RingHom f a) b) (p.eval₂ (eval₂RingHom f a') b') ∧
      v (p.eval₂ (eval₂RingHom f a') b') ≤ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [eval₂_add, eval₂_add]
    exact ⟨hp.1.add hq.1, (v.map_add _ _).trans (max_le hp.2 hq.2)⟩
  | monomial n q =>
    rw [eval₂_monomial, eval₂_monomial, coe_eval₂RingHom, coe_eval₂RingHom]
    have hq := Cong.eval₂ f hf ha ha' q
    have hpow : v (b' ^ n) ≤ 1 := by rw [Valuation.map_pow]; exact pow_le_one' hb' n
    exact ⟨hq.1.mul (hb.pow hb' n) hq.2 hpow, by rw [Valuation.map_mul]; exact mul_le_one' hq.2 hpow⟩

end Eval

end Valuation

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {R' : Type*} [CommRing R'] [IsDedekindDomain R'] {K' : Type*} [Field K']
  [Algebra R' K'] [IsFractionRing R' K']

omit [IsDedekindDomain R] [IsFractionRing R K] in

theorem valuation_map_le_exp_neg_of_mem_pow (ψ : K →+* K') (w : HeightOneSpectrum R)
    (v : HeightOneSpectrum R')
    (h0 : ∀ b : R, v.valuation K' (ψ (algebraMap R K b)) ≤ 1)
    (h1 : ∀ b : R, b ∈ w.asIdeal → v.valuation K' (ψ (algebraMap R K b)) ≤ exp (-1 : ℤ))
    (m : ℕ) : ∀ a ∈ w.asIdeal ^ m, v.valuation K' (ψ (algebraMap R K a)) ≤ exp (-(m : ℤ)) := by
  induction m with
  | zero =>
    intro a _
    rw [Nat.cast_zero, neg_zero, exp_zero]
    exact h0 a
  | succ m ih =>
    intro a ha
    rw [pow_succ'] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro c hc a' ha'
      rw [map_mul, map_mul, map_mul, Nat.cast_succ, neg_add, add_comm, exp_add]
      exact mul_le_mul' (h1 c hc) (ih a' ha')
    · intro z₁ z₂ hz₁ hz₂
      rw [map_add, map_add]
      exact (Valuation.map_add _ _ _).trans (max_le hz₁ hz₂)

theorem valuation_map_le_of_valuation_le (ψ : K →+* K') (w : HeightOneSpectrum R)
    (v : HeightOneSpectrum R')
    (h1 : ∀ b : R, b ∈ w.asIdeal → v.valuation K' (ψ (algebraMap R K b)) ≤ exp (-1 : ℤ))
    (h2 : ∀ b : R, b ∉ w.asIdeal → v.valuation K' (ψ (algebraMap R K b)) = 1)
    (x : K) (k : ℕ) (hx : w.valuation K x ≤ exp (-(k : ℤ))) :
    v.valuation K' (ψ x) ≤ exp (-(k : ℤ)) := by
  have h0 : ∀ b : R, v.valuation K' (ψ (algebraMap R K b)) ≤ 1 := by
    intro b
    by_cases hb : b ∈ w.asIdeal
    · exact (h1 b hb).trans (by rw [← exp_zero, exp_le_exp]; norm_num)
    · exact (h2 b hb).le
  have hx1 : w.valuation K x ≤ 1 :=
    hx.trans (by rw [← exp_zero, exp_le_exp, neg_nonpos]; exact Nat.cast_nonneg k)
  obtain ⟨n, d, hnd⟩ := exists_primeCompl_mul_eq_of_integer (v := w) x hx1
  have hd : (d : R) ∉ w.asIdeal := d.2

  have hwn : w.valuation K (algebraMap R K n) ≤ exp (-(k : ℤ)) := by
    rw [← hnd, map_mul, (valuation_eq_one_iff_notMem (K := K) w).mpr hd, mul_one]
    exact hx
  rw [valuation_of_algebraMap, intValuation_le_pow_iff_mem] at hwn
  have hψn := valuation_map_le_exp_neg_of_mem_pow ψ w v h0 h1 k n hwn

  have := congrArg (fun t => v.valuation K' (ψ t)) hnd
  simp only [map_mul, h2 d hd, mul_one] at this
  rw [this]
  exact hψn

end IsDedekindDomain.HeightOneSpectrum

namespace WeierstrassCurve.Affine

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial

section Transport

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]

theorem _root_.WithZero.lt_one_iff_le_exp_neg_one {y : ℤᵐ⁰} : y < 1 ↔ y ≤ exp (-1 : ℤ) := by
  by_cases hy : y = 0
  · subst hy; simp
  · rw [← exp_log hy, ← exp_zero, exp_lt_exp, exp_le_exp]; omega

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in

theorem valuation_algebraMap_le_one (P : (W⁄K).Point) (hP : P ≠ 0) (c : K) :
    (placeOf W K P hP).valuation (W⁄K).FunctionField (algebraMap K (W⁄K).FunctionField c) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField]
  exact valuation_le_one _ _

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in

theorem valuation_algebraMap_eq_one (P : (W⁄K).Point) (hP : P ≠ 0) {c : K} (hc : c ≠ 0) :
    (placeOf W K P hP).valuation (W⁄K).FunctionField (algebraMap K (W⁄K).FunctionField c) = 1 := by
  apply le_antisymm (valuation_algebraMap_le_one W K P hP c)
  have h := valuation_algebraMap_le_one W K P hP c⁻¹
  rw [map_inv₀, map_inv₀, inv_le_one₀] at h
  · exact h
  · rw [Valuation.pos_iff]
    exact (_root_.map_ne_zero _).mpr hc

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] in

theorem mem_placeOf_iff (P : (W⁄K).Point) (hP : P ≠ 0) (b : (W⁄K).CoordinateRing) :
    b ∈ (placeOf W K P hP).asIdeal ↔ CoordinateRing.evalAt W K (Point.nonsingular_xc_yc hP).left b = 0 := by
  constructor
  · exact CoordinateRing.evalAt_XYIdeal W K _ b
  · intro hb
    have hker : RingHom.ker (CoordinateRing.evalAt W K (Point.nonsingular_xc_yc hP).left) =
        (placeOf W K P hP).asIdeal := by
      refine ((CoordinateRing.XYIdeal_isMaximal (Point.nonsingular_xc_yc hP).left).eq_of_le
        (RingHom.ker_ne_top _) ?_).symm
      intro g hg
      exact (RingHom.mem_ker).mpr (CoordinateRing.evalAt_XYIdeal W K _ g hg)
    rw [← hker]
    exact (RingHom.mem_ker).mpr hb

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
theorem cong_genericX (P : (W⁄K).Point) (hP : P ≠ 0) :
    ((placeOf W K P hP).valuation (W⁄K).FunctionField).Cong (genericX W K)
      (algebraMap K (W⁄K).FunctionField P.xc) := by
  rw [Valuation.cong_iff, IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField, genericX,
    ← map_sub]
  apply (valuation_lt_one_iff_mem _ _).mpr
  rw [placeOf_asIdeal]
  have : CoordinateRing.mk (W⁄K) (C X) - algebraMap K (W⁄K).CoordinateRing P.xc =
      CoordinateRing.XClass (W⁄K) P.xc := by
    rw [CoordinateRing.XClass, map_sub, map_sub]; rfl
  rw [this]
  exact Ideal.subset_span (Set.mem_insert _ _)

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
theorem cong_genericY (P : (W⁄K).Point) (hP : P ≠ 0) :
    ((placeOf W K P hP).valuation (W⁄K).FunctionField).Cong (genericY W K)
      (algebraMap K (W⁄K).FunctionField P.yc) := by
  rw [Valuation.cong_iff, IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField, genericY,
    ← map_sub]
  apply (valuation_lt_one_iff_mem _ _).mpr
  rw [placeOf_asIdeal]
  have : CoordinateRing.mk (W⁄K) Y - algebraMap K (W⁄K).CoordinateRing P.yc =
      CoordinateRing.YClass (W⁄K) (C P.yc) := by
    rw [CoordinateRing.YClass, map_sub]; rfl
  rw [this]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] in

theorem algebraMap_evalEval (g : K[X][Y]) (a b : K) :
    algebraMap K (W⁄K).FunctionField (g.evalEval a b) =
      g.eval₂ (eval₂RingHom (algebraMap K (W⁄K).FunctionField) (algebraMap K _ a)) (algebraMap K _ b) := by
  have hφ : (algebraMap K (W⁄K).FunctionField).comp (evalEvalRingHom a b) =
      eval₂RingHom (eval₂RingHom (algebraMap K (W⁄K).FunctionField) (algebraMap K _ a)) (algebraMap K _ b) := by
    apply Polynomial.ringHom_ext
    · intro q
      simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_C, coe_eval₂RingHom,
        eval₂_C, eval₂_at_apply]
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_X, eval_C, coe_eval₂RingHom,
        eval₂_X]
  exact RingHom.congr_fun hφ g

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] in
theorem pointHom_mk_eq_eval₂ (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) (g : K[X][Y]) :
    pointHom Q hQ (CoordinateRing.mk (W⁄K) g) =
      g.eval₂ (eval₂RingHom (algebraMap K (W⁄K).FunctionField) Q.xc) Q.yc := by
  rw [pointHom_mk]
  congr 1

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in

theorem valuation_pointPull_le (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) {P : (W⁄K).Point} (hP : P ≠ 0) {P' : (W⁄K).Point}
    (hP' : P' ≠ 0)
    (hx : ((placeOf W K P hP).valuation (W⁄K).FunctionField).Cong Q.xc (algebraMap K _ P'.xc))
    (hy : ((placeOf W K P hP).valuation (W⁄K).FunctionField).Cong Q.yc (algebraMap K _ P'.yc))
    (h : (W⁄K).FunctionField) (k : ℕ)
    (hh : (placeOf W K P' hP').valuation (W⁄K).FunctionField h ≤ exp (-(k : ℤ))) :
    (placeOf W K P hP).valuation (W⁄K).FunctionField (pointPull Q hQ hinj h) ≤ exp (-(k : ℤ)) := by
  set v := (placeOf W K P hP).valuation (W⁄K).FunctionField with hv
  have hc : ∀ g : K[X][Y], v.Cong (pointHom Q hQ (CoordinateRing.mk (W⁄K) g))
      (algebraMap K _ (g.evalEval P'.xc P'.yc)) := by
    intro g
    rw [pointHom_mk_eq_eval₂, algebraMap_evalEval]
    exact (Valuation.Cong.eval₂_eval₂ (v := v) (algebraMap K _) (valuation_algebraMap_le_one W K P hP)
      hx (valuation_algebraMap_le_one W K P hP _) hy (valuation_algebraMap_le_one W K P hP _) g).1
  refine valuation_map_le_of_valuation_le (pointPull Q hQ hinj : (W⁄K).FunctionField →+* (W⁄K).FunctionField)
    (placeOf W K P' hP') (placeOf W K P hP) ?_ ?_ h k hh
  · intro b hb
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    change v (pointPull Q hQ hinj (algebraMap _ _ (CoordinateRing.mk (W⁄K) g))) ≤ _
    rw [pointPull_algebraMap, ← lt_one_iff_le_exp_neg_one, ← Valuation.cong_zero_iff]
    have h0 : g.evalEval P'.xc P'.yc = 0 := by
      rw [← CoordinateRing.evalAt_mk W K (Point.nonsingular_xc_yc hP').left]
      exact (mem_placeOf_iff W K P' hP' _).mp hb
    simpa only [h0, map_zero] using hc g
  · intro b hb
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    change v (pointPull Q hQ hinj (algebraMap _ _ (CoordinateRing.mk (W⁄K) g))) = 1
    rw [pointPull_algebraMap]
    have h0 : g.evalEval P'.xc P'.yc ≠ 0 := by
      rw [← CoordinateRing.evalAt_mk W K (Point.nonsingular_xc_yc hP').left]
      exact fun h => hb ((mem_placeOf_iff W K P' hP' _).mpr h)
    exact (hc g).eq_of_eq_one (valuation_algebraMap_eq_one W K P hP h0)

theorem valuation_mulPull_le {n : ℤ} (hgood : MulGood W K n) (Φ Ψ : K[X]) (ω ψ : K[X][Y])
    (hξ : (n • genericPoint W K).xc =
      Φ.eval₂ (algebraMap K (W⁄K).FunctionField) (genericX W K) /
        Ψ.eval₂ (algebraMap K (W⁄K).FunctionField) (genericX W K))
    (hη : (n • genericPoint W K).yc =
      ω.eval₂ (eval₂RingHom (algebraMap K (W⁄K).FunctionField) (genericX W K)) (genericY W K) /
        ψ.eval₂ (eval₂RingHom (algebraMap K (W⁄K).FunctionField) (genericX W K)) (genericY W K) ^ 3)
    {P : (W⁄K).Point} (hP : P ≠ 0) (hnP : n • P ≠ 0)
    (hxP : (n • P).xc = Φ.eval P.xc / Ψ.eval P.xc) (hΨ : Ψ.eval P.xc ≠ 0)
    (hyP : (n • P).yc = ω.evalEval P.xc P.yc / ψ.evalEval P.xc P.yc ^ 3) (hψ : ψ.evalEval P.xc P.yc ≠ 0)
    (h : (W⁄K).FunctionField) (k : ℕ)
    (hh : (placeOf W K (n • P) hnP).valuation (W⁄K).FunctionField h ≤ exp (-(k : ℤ))) :
    (placeOf W K P hP).valuation (W⁄K).FunctionField (mulPull W K n hgood h) ≤ exp (-(k : ℤ)) := by
  set v := (placeOf W K P hP).valuation (W⁄K).FunctionField with hv
  have hc1 := valuation_algebraMap_le_one W K P hP
  have hX := cong_genericX W K P hP
  have hY := cong_genericY W K P hP

  have hx : v.Cong (n • genericPoint W K).xc (algebraMap K _ (n • P).xc) := by
    rw [hξ, hxP, map_div₀, ← eval₂_at_apply, ← eval₂_at_apply]
    have hΦ := Valuation.Cong.eval₂ (v := v) (algebraMap K _) hc1 hX (hc1 _) Φ
    have hΨc := Valuation.Cong.eval₂ (v := v) (algebraMap K _) hc1 hX (hc1 _) Ψ
    refine hΦ.1.div hΨc.1 hΦ.2 ?_
    rw [eval₂_at_apply]
    exact valuation_algebraMap_eq_one W K P hP hΨ

  have hy : v.Cong (n • genericPoint W K).yc (algebraMap K _ (n • P).yc) := by
    rw [hη, hyP, map_div₀, map_pow, algebraMap_evalEval, algebraMap_evalEval]
    have hω := Valuation.Cong.eval₂_eval₂ (v := v) (algebraMap K _) hc1 hX (hc1 _) hY (hc1 _) ω
    have hψc := Valuation.Cong.eval₂_eval₂ (v := v) (algebraMap K _) hc1 hX (hc1 _) hY (hc1 _) ψ
    refine hω.1.div (hψc.1.pow hψc.2 3) hω.2 ?_
    rw [← algebraMap_evalEval, ← map_pow]
    exact valuation_algebraMap_eq_one W K P hP (pow_ne_zero 3 hψ)
  rw [mulPull_eq W K hgood]
  exact valuation_pointPull_le W K _ _ _ hP hnP hx hy h k hh

end Transport

end WeierstrassCurve.Affine

open WeierstrassCurve.Affine

namespace FunctionFieldPullback.SmulZero

set_option autoImplicit false

theorem solution {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔ (W.ψ n).evalEval x y = 0 :=
  W.smul_eq_zero_iff_evalEval_ψ h n
end FunctionFieldPullback.SmulZero


theorem WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔ (W.ψ n).evalEval x y = 0 :=
  FunctionFieldPullback.SmulZero.solution W h n

namespace FunctionFieldPullback.NatDeg

open Polynomial

theorem PortCard.natDegree_Φ_sub_C_mul_ΨSq {R : Type*} [CommRing R] [Nontrivial R]
    (W : WeierstrassCurve R) (n : ℤ) (c : R) :
    (W.Φ n - C c * W.ΨSq n).natDegree = n.natAbs ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [WeierstrassCurve.Φ_zero, WeierstrassCurve.ΨSq_zero, mul_zero, sub_zero, natDegree_one,
      Int.natAbs_zero, zero_pow two_ne_zero]
  · have h1 : 1 ≤ n.natAbs ^ 2 := Nat.one_le_pow _ _ (Int.natAbs_pos.mpr hn)
    rw [natDegree_sub_eq_left_of_natDegree_lt, WeierstrassCurve.natDegree_Φ]
    calc (C c * W.ΨSq n).natDegree ≤ (W.ΨSq n).natDegree := natDegree_C_mul_le _ _
      _ ≤ n.natAbs ^ 2 - 1 := WeierstrassCurve.natDegree_ΨSq_le W n
      _ < n.natAbs ^ 2 := Nat.sub_lt (by omega) one_pos
      _ = (W.Φ n).natDegree := (WeierstrassCurve.natDegree_Φ W n).symm

theorem solution {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) (n : ℤ) (c : R) : (W.Φ n - Polynomial.C c * W.ΨSq n).natDegree = n.natAbs ^ 2 :=
  PortCard.natDegree_Φ_sub_C_mul_ΨSq W n c
end FunctionFieldPullback.NatDeg


theorem WeierstrassCurve.natDegree_Phi_sub_C_mul_PsiSq {R : Type*} [CommRing R] [Nontrivial R] (W : WeierstrassCurve R) (n : ℤ) (c : R) : (W.Φ n - Polynomial.C c * W.ΨSq n).natDegree = n.natAbs ^ 2 :=
  FunctionFieldPullback.NatDeg.solution W n c

namespace FunctionFieldPullback.EvalPsi

open Polynomial
open scoped Polynomial.Bivariate

theorem PortCard.evalEval_ψ_sq {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  have hmk : WeierstrassCurve.Affine.CoordinateRing.mk W (W.ψ n ^ 2) =
      WeierstrassCurve.Affine.CoordinateRing.mk W (C (W.ΨSq n)) := by
    rw [map_pow, WeierstrassCurve.Affine.CoordinateRing.mk_ψ,
      WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq]
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp hmk
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_pow, evalEval_C] at h1
  exact h1

theorem PortCard.evalEval_φ {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y) (n : ℤ) : (W.φ n).evalEval x y = (W.Φ n).eval x := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp (WeierstrassCurve.Affine.CoordinateRing.mk_φ W n)
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_C] at h1
  exact h1

theorem solution {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x :=
  PortCard.evalEval_ψ_sq W h n
end FunctionFieldPullback.EvalPsi


theorem WeierstrassCurve.Affine.evalEval_psi_sq {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x :=
  FunctionFieldPullback.EvalPsi.solution W h n

namespace FunctionFieldPullback.Psi2

open Polynomial

theorem PortCard.sub_negY_sq_eq_eval_Ψ₂Sq {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    {x y : R} (e : W.toAffine.Equation x y) :
    (y - W.toAffine.negY x y) ^ 2 = W.Ψ₂Sq.eval x := by
  rw [WeierstrassCurve.Affine.equation_iff] at e
  simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination 4 * e

theorem PortCard.two_smul_some_eq_zero_iff {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) :
    2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ W.Ψ₂Sq.eval x = 0 := by
  have key : 2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ y = W.toAffine.negY x y := by
    rw [two_nsmul, add_eq_zero_iff_eq_neg, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    simp
  rw [key, ← PortCard.sub_negY_sq_eq_eval_Ψ₂Sq W h.left, pow_eq_zero_iff two_ne_zero, sub_eq_zero]

theorem PortCard.Ψ₂Sq_ne_zero_of_isElliptic {F : Type*} [Field F] (W : WeierstrassCurve F)
    [W.IsElliptic] : W.Ψ₂Sq ≠ 0 := by
  intro h0
  rw [WeierstrassCurve.Ψ₂Sq_eq, Cubic.toPoly_eq_zero_iff] at h0
  have h4 : (4 : F) = 0 := congrArg Cubic.a h0
  have hb₂ : W.b₂ = 0 := congrArg Cubic.b h0
  have hb₆ : W.b₆ = 0 := congrArg Cubic.d h0
  have h2 : (2 : F) = 0 := by
    have h22 : (2 : F) * 2 = 0 := by linear_combination h4
    rcases mul_eq_zero.mp h22 with h | h <;> exact h
  have hΔ : W.Δ = 0 := by
    rw [show W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆
      from rfl]
    linear_combination (-W.b₂ * W.b₈ + 9 * W.b₄ * W.b₆) * hb₂ + (-27 * W.b₆) * hb₆ +
      (-4 * W.b₄ ^ 3) * h2
  exact W.isUnit_Δ.ne_zero hΔ

theorem solution {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] : W.Ψ₂Sq ≠ 0 :=
  PortCard.Ψ₂Sq_ne_zero_of_isElliptic W
end FunctionFieldPullback.Psi2


theorem WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] : W.Ψ₂Sq ≠ 0 :=
  FunctionFieldPullback.Psi2.solution W

namespace FunctionFieldPullback.ZsmulDiv

section PortCardMulX

namespace PortCard

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point Polynomial
open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem zsmul_some_eq_some_of_evalEval_ψ_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) :
    ∃ (x' y' : F) (h' : W.toAffine.Nonsingular x' y'),
      n • Point.some x y h = Point.some x' y' h' ∧
        x' * (W.ψ n).evalEval x y ^ 2 = (W.φ n).evalEval x y ∧
        x' * (W.ΨSq n).eval x = (W.Φ n).eval x := by
  have heq : W.toAffine.Equation x y := h.left
  have hψsq := W.evalEval_ψ_sq heq n
  have key := zsmul_eq_smulEval W h n
  have hVz : smulEval W x y n 2 ≠ 0 := hψ
  have hV := key ▸ (n • Jacobian.Point.fromAffine (Point.some x y h)).nonsingular
  have hQeq : (n • Jacobian.Point.fromAffine (Point.some x y h)) =
      Jacobian.Point.mk hV := Jacobian.Point.ext key
  refine ⟨smulEval W x y n 0 / smulEval W x y n 2 ^ 2,
    smulEval W x y n 1 / smulEval W x y n 2 ^ 3,
    (Jacobian.nonsingular_of_Z_ne_zero hVz).mp hV, ?_, ?_, ?_⟩
  · calc n • Point.some x y h
        = Jacobian.Point.toAffineAddEquiv W
            (n • Jacobian.Point.fromAffine (Point.some x y h)) := by
          rw [map_zsmul, ← Jacobian.Point.toAffineAddEquiv_symm_apply,
            AddEquiv.apply_symm_apply]
      _ = _ := by
          rw [hQeq, Jacobian.Point.toAffineAddEquiv_apply]
          exact Jacobian.Point.toAffineLift_of_Z_ne_zero hVz
  · show (W.φ n).evalEval x y / (W.ψ n).evalEval x y ^ 2 * (W.ψ n).evalEval x y ^ 2 =
        (W.φ n).evalEval x y
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 hψ)]
  · show (W.φ n).evalEval x y / (W.ψ n).evalEval x y ^ 2 * (W.ΨSq n).eval x = (W.Φ n).eval x
    rw [← hψsq, div_mul_cancel₀ _ (pow_ne_zero 2 hψ), W.evalEval_φ heq]

theorem zsmul_some_eq_some_of_eval_ΨSq_ne_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : (W.ΨSq n).eval x ≠ 0) :
    ∃ (x' y' : F) (h' : W.toAffine.Nonsingular x' y'),
      n • Point.some x y h = Point.some x' y' h' ∧ x' * (W.ΨSq n).eval x = (W.Φ n).eval x := by
  have hψ : (W.ψ n).evalEval x y ≠ 0 := fun h0 =>
    hn (by rw [← W.evalEval_ψ_sq h.left n, h0]; exact zero_pow two_ne_zero)
  obtain ⟨x', y', h', hP, -, hx⟩ := zsmul_some_eq_some_of_evalEval_ψ_ne_zero W h hψ
  exact ⟨x', y', h', hP, hx⟩

theorem zsmul_some_eq_zero_iff_eval_ΨSq {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • Point.some x y h = 0 ↔ (W.ΨSq n).eval x = 0 := by
  rw [W.smul_eq_zero_iff_evalEval_ψ h n, ← W.evalEval_ψ_sq h.left n]
  exact ⟨fun h0 => by rw [h0]; exact zero_pow two_ne_zero, fun h0 => (sq_eq_zero_iff).mp h0⟩

theorem zsmul_some_eq_some_div {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ}
    (hψ : (W.ψ n).evalEval x y ≠ 0) :
    ∃ (y' : F) (h' : W.toAffine.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'),
      n • Point.some x y h = Point.some ((W.Φ n).eval x / (W.ΨSq n).eval x) y' h' := by
  obtain ⟨x', y', h', hP, -, hx⟩ := zsmul_some_eq_some_of_evalEval_ψ_ne_zero W h hψ
  have hΨ : (W.ΨSq n).eval x ≠ 0 := by
    rw [← W.evalEval_ψ_sq h.left n]; exact pow_ne_zero 2 hψ
  obtain rfl : x' = (W.Φ n).eval x / (W.ΨSq n).eval x := by rw [eq_div_iff hΨ]; exact hx
  exact ⟨y', h', hP⟩

end PortCard

end PortCardMulX

theorem solution {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) : ∃ (y' : F) (h' : W.toAffine.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'), n • WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some ((W.Φ n).eval x / (W.ΨSq n).eval x) y' h' :=
  PortCard.zsmul_some_eq_some_div W h hψ
end FunctionFieldPullback.ZsmulDiv


theorem WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ} (hψ : (W.ψ n).evalEval x y ≠ 0) : ∃ (y' : F) (h' : W.toAffine.Nonsingular ((W.Φ n).eval x / (W.ΨSq n).eval x) y'), n • WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some ((W.Φ n).eval x / (W.ΨSq n).eval x) y' h' :=
  FunctionFieldPullback.ZsmulDiv.solution W h hψ

namespace FunctionFieldPullback.TwoSmul

theorem solution {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) : 2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ W.Ψ₂Sq.eval x = 0 :=
  FunctionFieldPullback.Psi2.PortCard.two_smul_some_eq_zero_iff W h
end FunctionFieldPullback.TwoSmul


theorem WeierstrassCurve.Affine.Point.two_smul_some_eq_zero_iff {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) : 2 • WeierstrassCurve.Affine.Point.some x y h = 0 ↔ W.Ψ₂Sq.eval x = 0 :=
  FunctionFieldPullback.TwoSmul.solution W h

namespace FunctionFieldPullback.AdjoinTop

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine
open WeierstrassCurve.Affine WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

open WeierstrassCurve.Affine.CoordinateRing in

theorem CoordinateRing.adjoin_mk_X_mk_Y :
    Algebra.adjoin K {CoordinateRing.mk W.toAffine (C X), CoordinateRing.mk W.toAffine Y} = ⊤ := by
  set x := CoordinateRing.mk W.toAffine (C X) with hx
  set y := CoordinateRing.mk W.toAffine Y with hy
  apply Algebra.eq_top_iff.mpr
  intro r
  induction r using AdjoinRoot.induction_on with
  | ih p =>

    have hC : ∀ c : K[X], CoordinateRing.mk W.toAffine (C c) ∈ Algebra.adjoin K {x, y} := by
      intro c
      have : CoordinateRing.mk W.toAffine (C c) = aeval x c := by
        have h1 : (CoordinateRing.mk W.toAffine).comp C = (aeval x : K[X] →ₐ[K] _).toRingHom := by
          apply Polynomial.ringHom_ext
          · intro k
            rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C]
            rfl
          · rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
        exact congrArg (fun f : K[X] →+* _ => f c) h1
      rw [this]
      exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
        (Polynomial.aeval_mem_adjoin_singleton K x)
    induction p using Polynomial.induction_on with
    | C c => exact hC c
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n c _ =>
      rw [map_mul, map_pow]
      exact mul_mem (hC c)
        (pow_mem (Algebra.subset_adjoin (Set.mem_insert_of_mem x (Set.mem_singleton y))) _)

end WeierstrassCurve.Affine

open _root_.WeierstrassCurve _root_.FunctionFieldPullback.AdjoinTop.WeierstrassCurve _root_.WeierstrassCurve.Affine _root_.FunctionFieldPullback.AdjoinTop.WeierstrassCurve.Affine in
theorem solution {K : Type*} [Field K] (W : WeierstrassCurve K) : IntermediateField.adjoin K {algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)), algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X)} = ⊤ := by
  set x := CoordinateRing.mk W.toAffine (C X)
  set y := CoordinateRing.mk W.toAffine Y
  set S : IntermediateField K W.toAffine.FunctionField := IntermediateField.adjoin K
    {algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField x,
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField y} with hS

  have hR : ∀ r : W.toAffine.CoordinateRing,
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField r ∈ S := by
    intro r
    let φ : W.toAffine.CoordinateRing →ₐ[K] W.toAffine.FunctionField :=
      IsScalarTower.toAlgHom K W.toAffine.CoordinateRing W.toAffine.FunctionField
    have hr : r ∈ (⊤ : Subalgebra K W.toAffine.CoordinateRing) := Algebra.mem_top
    rw [← CoordinateRing.adjoin_mk_X_mk_Y W] at hr
    have himg : φ r ∈ (Algebra.adjoin K {x, y}).map φ := Subalgebra.mem_map.mpr ⟨r, hr, rfl⟩
    rw [AlgHom.map_adjoin] at himg
    have hle : Algebra.adjoin K (φ '' {x, y}) ≤ S.toSubalgebra := by
      rw [Set.image_pair]
      exact IntermediateField.algebra_adjoin_le_adjoin K _
    exact hle himg
  apply eq_top_iff.mpr
  intro z _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W.toAffine.CoordinateRing) z
  exact div_mem (hR a) (hR b)
end FunctionFieldPullback.AdjoinTop


theorem WeierstrassCurve.Affine.FunctionField.adjoin_X_Y_eq_top {K : Type*} [Field K] (W : WeierstrassCurve K) : IntermediateField.adjoin K {algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)), algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X)} = ⊤ :=
  FunctionFieldPullback.AdjoinTop.solution W

namespace FunctionFieldPullback.Span

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace WeilPairingND

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

lemma le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (hx : x < 1) : x ≤ exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← exp_log h0] at hx ⊢
    rw [← exp_zero, exp_lt_exp] at hx
    rw [exp_le_exp]
    omega

omit [IsDedekindDomain R] in

lemma isUnit_of_forall_not_mem [IsDomain R] {r : R} (hr : ∀ w : HeightOneSpectrum R, r ∉ w.asIdeal)
    (w₀ : HeightOneSpectrum R) : IsUnit r := by
  by_contra hu
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal (Ideal.span {r}) (Ideal.span_singleton_ne_top hu)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr w₀ (Submodule.zero_mem _)
  have h𝔪0 : 𝔪 ≠ ⊥ := fun h => by
    rw [h, le_bot_iff, Ideal.span_singleton_eq_bot] at hle
    exact hr0 hle
  exact hr ⟨𝔪, h𝔪.isPrime, h𝔪0⟩ (hle (Ideal.mem_span_singleton_self r))

theorem exists_eq_span_of_eq_pullback (μ : K →+* K)
    (N : HeightOneSpectrum R → Option (HeightOneSpectrum R)) (hN : ∀ w, ∃ v, N v = some w)
    (hμ : ∀ v w, N v = some w → ∀ (h : K) (k : ℕ),
      w.valuation K h ≤ exp (-(k : ℤ)) → v.valuation K (μ h) ≤ exp (-(k : ℤ)))
    (g : K) (t₀ : HeightOneSpectrum R) (hg₀ : ∀ v, N v = some t₀ → v.valuation K g = exp (-1))
    (hg₁ : ∀ v w, N v = some w → w ≠ t₀ → v.valuation K g = 1) (hgμ : ∃ h, μ h = g) :
    ∃ r : R, t₀.asIdeal = Ideal.span {r} := by
  obtain ⟨h, rfl⟩ := hgμ
  obtain ⟨v₀, hv₀⟩ := hN t₀

  have hg_le : ∀ v w, N v = some w → v.valuation K (μ h) ≤ 1 := by
    intro v w hvw
    by_cases hw : w = t₀
    · subst hw; rw [hg₀ v hvw, ← exp_zero, exp_le_exp]; norm_num
    · rw [hg₁ v w hvw hw]
  have hμ0 : ∀ v w, N v = some w → ∀ x : K, w.valuation K x ≤ 1 → v.valuation K (μ x) ≤ 1 := by
    intro v w hvw x hx
    have := hμ v w hvw x 0 (by rwa [Nat.cast_zero, neg_zero, exp_zero])
    rwa [Nat.cast_zero, neg_zero, exp_zero] at this
  have hh0 : h ≠ 0 := by
    rintro rfl
    have := hg₀ v₀ hv₀
    rw [map_zero, Valuation.map_zero] at this
    exact WithZero.zero_ne_coe this
  have hμh0 : μ h ≠ 0 := (map_ne_zero μ).mpr hh0

  have h1 : ∀ w : HeightOneSpectrum R, w.valuation K h ≤ 1 := by
    intro w
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨v, hv⟩ := hN w
    have hinv : w.valuation K h⁻¹ ≤ exp (-((1 : ℕ) : ℤ)) := by
      rw [Nat.cast_one, map_inv₀]
      exact le_exp_neg_one_of_lt_one ((inv_lt_one₀ (lt_trans zero_lt_one hlt)).mpr hlt)
    have := hμ v w hv h⁻¹ 1 hinv
    rw [map_inv₀, map_inv₀, Nat.cast_one] at this
    have hlt' : (v.valuation K (μ h))⁻¹ < 1 := lt_of_le_of_lt this (by
      rw [← exp_zero, exp_lt_exp]; norm_num)
    have hpos : 0 < v.valuation K (μ h) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hμh0)
    exact absurd ((inv_lt_one₀ hpos).mp hlt') (not_lt.mpr (hg_le v w hv))

  obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one K h h1
  subst hr
  have hr0 : r ≠ 0 := fun h0 => hh0 (by rw [h0, map_zero])

  have h3 : ∀ w : HeightOneSpectrum R, w ≠ t₀ → r ∉ w.asIdeal := by
    intro w hw hmem
    obtain ⟨v, hv⟩ := hN w
    have hlt : w.valuation K (algebraMap R K r) ≤ exp (-((1 : ℕ) : ℤ)) := by
      rw [Nat.cast_one]
      exact le_exp_neg_one_of_lt_one ((valuation_lt_one_iff_mem w r).mpr hmem)
    have := hμ v w hv _ 1 hlt
    rw [hg₁ v w hv hw, Nat.cast_one, ← exp_zero, exp_le_exp] at this
    norm_num at this

  have h4a : r ∈ t₀.asIdeal := by
    by_contra hnot
    have hunit : IsUnit r := isUnit_of_forall_not_mem
      (fun w => by by_cases hw : w = t₀ <;> [exact hw ▸ hnot; exact h3 w hw]) t₀
    obtain ⟨u, hu⟩ := hunit
    have hprod : v₀.valuation K (μ (algebraMap R K r)) *
        v₀.valuation K (μ (algebraMap R K ((u⁻¹ : Rˣ) : R))) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, ← hu, Units.mul_inv, map_one, map_one, map_one]
    have hle : v₀.valuation K (μ (algebraMap R K ((u⁻¹ : Rˣ) : R))) ≤ 1 :=
      hμ0 v₀ t₀ hv₀ _ (valuation_le_one t₀ _)
    have key : v₀.valuation K (μ (algebraMap R K r)) *
        v₀.valuation K (μ (algebraMap R K ((u⁻¹ : Rˣ) : R))) ≤ exp (-1) * 1 := by
      rw [hg₀ v₀ hv₀]
      gcongr
    rw [hprod, mul_one, ← exp_zero, exp_le_exp] at key
    norm_num at key

  have h4b : r ∉ t₀.asIdeal ^ 2 := by
    intro hmem
    have hle : t₀.valuation K (algebraMap R K r) ≤ exp (-((2 : ℕ) : ℤ)) := by
      rw [valuation_of_algebraMap]
      exact (intValuation_le_pow_iff_mem t₀ r 2).mpr hmem
    have := hμ v₀ t₀ hv₀ _ 2 hle
    rw [hg₀ v₀ hv₀, exp_le_exp] at this
    norm_num at this

  refine ⟨r, ?_⟩
  have hdvd : t₀.asIdeal ∣ Ideal.span {r} :=
    (Ideal.dvd_span_singleton).mpr h4a
  obtain ⟨J, hJ⟩ := hdvd
  suffices hJtop : J = ⊤ by rw [hJ, hJtop, Ideal.mul_top]
  by_contra hJtop
  obtain ⟨𝔪, h𝔪, hJle⟩ := Ideal.exists_le_maximal J hJtop
  have hJ0 : J ≠ ⊥ := by
    intro hJ0
    rw [hJ0, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ
    exact hr0 hJ
  have h𝔪0 : 𝔪 ≠ ⊥ := fun h => hJ0 (le_bot_iff.mp (h ▸ hJle))
  set w : HeightOneSpectrum R := ⟨𝔪, h𝔪.isPrime, h𝔪0⟩
  have hrw : r ∈ t₀.asIdeal * w.asIdeal := by
    have : t₀.asIdeal * w.asIdeal ∣ Ideal.span {r} := by
      rw [hJ]; exact mul_dvd_mul_left _ ((Ideal.dvd_iff_le).mpr hJle)
    exact (Ideal.dvd_span_singleton).mp this
  by_cases hw : w = t₀
  · apply h4b
    rw [sq, ← hw]
    nth_rewrite 1 [hw]
    exact hrw
  · exact h3 w hw (Ideal.mul_le_right hrw)

end WeilPairingND

theorem solution {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (μ : K →+* K) (N : IsDedekindDomain.HeightOneSpectrum R → Option (IsDedekindDomain.HeightOneSpectrum R)) (hN : ∀ w, ∃ v, N v = some w) (hμ : ∀ v w, N v = some w → ∀ (h : K) (k : ℕ), w.valuation K h ≤ WithZero.exp (-(k : ℤ)) → v.valuation K (μ h) ≤ WithZero.exp (-(k : ℤ))) (g : K) (t₀ : IsDedekindDomain.HeightOneSpectrum R) (hg₀ : ∀ v, N v = some t₀ → v.valuation K g = WithZero.exp (-1)) (hg₁ : ∀ v w, N v = some w → w ≠ t₀ → v.valuation K g = 1) (hgμ : ∃ h, μ h = g) : ∃ r : R, t₀.asIdeal = Ideal.span {r} :=
  WeilPairingND.exists_eq_span_of_eq_pullback μ N hN hμ g t₀ hg₀ hg₁ hgμ
end FunctionFieldPullback.Span


theorem IsDedekindDomain.HeightOneSpectrum.exists_eq_span_singleton_of_map_eq {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (μ : K →+* K) (N : IsDedekindDomain.HeightOneSpectrum R → Option (IsDedekindDomain.HeightOneSpectrum R)) (hN : ∀ w, ∃ v, N v = some w) (hμ : ∀ v w, N v = some w → ∀ (h : K) (k : ℕ), w.valuation K h ≤ WithZero.exp (-(k : ℤ)) → v.valuation K (μ h) ≤ WithZero.exp (-(k : ℤ))) (g : K) (t₀ : IsDedekindDomain.HeightOneSpectrum R) (hg₀ : ∀ v, N v = some t₀ → v.valuation K g = WithZero.exp (-1)) (hg₁ : ∀ v w, N v = some w → w ≠ t₀ → v.valuation K g = 1) (hgμ : ∃ h, μ h = g) : ∃ r : R, t₀.asIdeal = Ideal.span {r} :=
  FunctionFieldPullback.Span.solution μ N hN hμ g t₀ hg₀ hg₁ hgμ

namespace FunctionFieldPullback.Exists

section PortGenNetIdentities

namespace Deep
namespace Gen

open WeierstrassCurve Polynomial

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable (W : WeierstrassCurve F)

theorem ΨSq_eval_eq_zero_of_preΨ {m : ℕ} {x₀ : K}
    (h : ((W.baseChange K).preΨ (m : ℤ)).eval x₀ = 0) :
    ((W.baseChange K).ΨSq m).eval x₀ = 0 := by
  rw [preΨ_ofNat] at h
  rw [ΨSq_ofNat, eval_mul, eval_pow, h, zero_pow two_ne_zero, zero_mul]

variable [IsAlgClosed K] [DecidableEq K]

theorem isCoprime_ΨSq_succ [W.IsElliptic] (n : ℕ) :
    IsCoprime ((W.baseChange K).ΨSq n) ((W.baseChange K).ΨSq (n + 1)) := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) (K := K)]
  intro x₀
  by_contra hcon
  push Not at hcon
  obtain ⟨hn0, hn1⟩ := hcon
  rw [coe_aeval_eq_eval] at hn0 hn1

  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root
    (C (1 : K) * X ^ 2 + C ((W.baseChange K).a₁ * x₀ + (W.baseChange K).a₃) * X +
      C (-(x₀ ^ 3 + (W.baseChange K).a₂ * x₀ ^ 2 + (W.baseChange K).a₄ * x₀ +
        (W.baseChange K).a₆)))
    (by rw [Polynomial.degree_quadratic one_ne_zero]; decide)
  have heq : (W.baseChange K).toAffine.Equation x₀ y₀ := by
    rw [Affine.equation_iff]
    simp only [IsRoot.def, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hy₀
    linear_combination hy₀
  have hns : (W.baseChange K).toAffine.Nonsingular x₀ y₀ :=
    (Affine.equation_iff_nonsingular).mp heq

  have hψ0 : ((W.baseChange K).ψ (n : ℤ)).evalEval x₀ y₀ = 0 := by
    have h2 := evalEval_ψ_sq (W.baseChange K) heq (n : ℤ)
    rw [hn0] at h2
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  have hψ1 : ((W.baseChange K).ψ ((n : ℤ) + 1)).evalEval x₀ y₀ = 0 := by
    have h2 := evalEval_ψ_sq (W.baseChange K) heq ((n : ℤ) + 1)
    rw [hn1] at h2
    exact (pow_eq_zero_iff two_ne_zero).mp h2

  have h0 : (n : ℤ) • (Affine.Point.some x₀ y₀ hns) = 0 :=
    (smul_eq_zero_iff_evalEval_ψ (W.baseChange K) hns (n : ℤ)).mpr hψ0
  have h1 : ((n : ℤ) + 1) • (Affine.Point.some x₀ y₀ hns) = 0 :=
    (smul_eq_zero_iff_evalEval_ψ (W.baseChange K) hns ((n : ℤ) + 1)).mpr hψ1
  have hP : (Affine.Point.some x₀ y₀ hns : (W.baseChange K).toAffine.Point) = 0 := by
    have hsub := sub_smul ((n : ℤ) + 1) (n : ℤ) (Affine.Point.some x₀ y₀ hns)
    rw [h1, h0, sub_zero, add_sub_cancel_left, one_smul] at hsub
    exact hsub
  exact Affine.Point.some_ne_zero hns hP

end Deep.Gen

end PortGenNetIdentities

section PortGenInduction

namespace Deep
namespace Gen

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

open scoped WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)

theorem smul_formula_or_zero [W.IsElliptic] {n : ℕ} (_hn : 0 < n) {x₀ y₀ : K}
    (h : (W.baseChange K).toAffine.Nonsingular x₀ y₀) :
    (((W.baseChange K).ΨSq n).eval x₀ ≠ 0 →
      ∃ (x' y' : K) (h' : (W.baseChange K).toAffine.Nonsingular x' y'),
        n • (Point.some x₀ y₀ h : W.toAffine⟮K⟯) = Point.some x' y' h' ∧
          x' * ((W.baseChange K).ΨSq n).eval x₀ = ((W.baseChange K).Φ n).eval x₀) ∧
    (((W.baseChange K).ΨSq n).eval x₀ = 0 →
      n • (Point.some x₀ y₀ h : W.toAffine⟮K⟯) = 0) := by
  have heq : (W.baseChange K).toAffine.Equation x₀ y₀ := h.left
  have hψsq := (W.baseChange K).evalEval_ψ_sq heq (n : ℤ)
  constructor
  ·
    intro hΨ
    have hψ : ((W.baseChange K).ψ (n : ℤ)).evalEval x₀ y₀ ≠ 0 := by
      intro h0
      exact hΨ (by rw [← hψsq, h0]; exact zero_pow two_ne_zero)
    have key := zsmul_eq_smulEval (W.baseChange K) h (n : ℤ)
    have hVz : smulEval (W.baseChange K) x₀ y₀ (n : ℤ) 2 ≠ 0 := hψ
    have hV := key ▸ ((n : ℤ) • Jacobian.Point.fromAffine (Point.some x₀ y₀ h)).nonsingular
    have hQeq : ((n : ℤ) • Jacobian.Point.fromAffine (Point.some x₀ y₀ h)) =
        Jacobian.Point.mk hV := Jacobian.Point.ext key
    refine ⟨smulEval (W.baseChange K) x₀ y₀ (n : ℤ) 0 /
        smulEval (W.baseChange K) x₀ y₀ (n : ℤ) 2 ^ 2,
      smulEval (W.baseChange K) x₀ y₀ (n : ℤ) 1 /
        smulEval (W.baseChange K) x₀ y₀ (n : ℤ) 2 ^ 3,
      (Jacobian.nonsingular_of_Z_ne_zero hVz).mp hV, ?_, ?_⟩
    · calc n • (Point.some x₀ y₀ h : W.toAffine⟮K⟯)
          = Jacobian.Point.toAffineAddEquiv (W.baseChange K)
            ((n : ℤ) • Jacobian.Point.fromAffine (Point.some x₀ y₀ h)) := by
            rw [map_zsmul, ← Jacobian.Point.toAffineAddEquiv_symm_apply,
              AddEquiv.apply_symm_apply, natCast_zsmul]
        _ = _ := by
            rw [hQeq, Jacobian.Point.toAffineAddEquiv_apply]
            exact Jacobian.Point.toAffineLift_of_Z_ne_zero hVz
    · show ((W.baseChange K).φ (n : ℤ)).evalEval x₀ y₀ /
          ((W.baseChange K).ψ (n : ℤ)).evalEval x₀ y₀ ^ 2 *
          ((W.baseChange K).ΨSq (n : ℤ)).eval x₀ =
          ((W.baseChange K).Φ (n : ℤ)).eval x₀
      rw [← hψsq, div_mul_cancel₀ _ (pow_ne_zero 2 hψ),
        (W.baseChange K).evalEval_φ heq]
  ·
    intro hΨ
    have hψ0 : ((W.baseChange K).ψ (n : ℤ)).evalEval x₀ y₀ = 0 :=
      sq_eq_zero_iff.mp (hψsq.trans hΨ)
    rw [← natCast_zsmul]
    exact ((W.baseChange K).smul_eq_zero_iff_evalEval_ψ h (n : ℤ)).mpr hψ0

end Deep.Gen

end PortGenInduction

section PortGenSmulFormula

namespace Deep
namespace Gen

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

open scoped WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)

theorem smul_x_eq [W.IsElliptic] {n : ℕ} (hn : 0 < n) {x₀ y₀ : K}
    (h : (W.baseChange K).toAffine.Nonsingular x₀ y₀)
    (hns : ((W.baseChange K).ΨSq n).eval x₀ ≠ 0) :
    ∃ (x' y' : K) (h' : (W.baseChange K).toAffine.Nonsingular x' y'),
      n • (Point.some x₀ y₀ h : W.toAffine⟮K⟯) = Point.some x' y' h' ∧
        x' * ((W.baseChange K).ΨSq n).eval x₀ = ((W.baseChange K).Φ n).eval x₀ :=
  (smul_formula_or_zero W hn h).1 hns

omit [DecidableEq K] in

private lemma eval_ne_of_isCoprime {f g : Polynomial K} (h : IsCoprime f g) {x₀ : K}
    (hf : f.eval x₀ = 0) (hg : g.eval x₀ = 0) : False := by
  obtain ⟨a, b, hab⟩ := h
  have h1 := congrArg (Polynomial.eval x₀) hab
  simp only [eval_add, eval_mul, hf, hg, mul_zero, add_zero, eval_one] at h1
  exact zero_ne_one h1

theorem isCoprime_Φ_ΨSq [IsAlgClosed K] [W.IsElliptic] {n : ℕ} (hn : 0 < n) :
    IsCoprime ((W.baseChange K).Φ n) ((W.baseChange K).ΨSq n) := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) (K := K)]
  intro x₀
  by_contra hcon
  push Not at hcon
  obtain ⟨hΦ0, hΨ0⟩ := hcon
  rw [coe_aeval_eq_eval] at hΦ0 hΨ0
  have hΦdef : (W.baseChange K).Φ (n : ℤ) =
      X * (W.baseChange K).ΨSq (n : ℤ) -
        (W.baseChange K).preΨ ((n : ℤ) + 1) * (W.baseChange K).preΨ ((n : ℤ) - 1) *
          (if Even (n : ℤ) then 1 else (W.baseChange K).Ψ₂Sq) := rfl
  have h0 : ((W.baseChange K).preΨ ((n : ℤ) + 1)).eval x₀ *
      ((W.baseChange K).preΨ ((n : ℤ) - 1)).eval x₀ *
      (if Even (n : ℤ) then (1 : K) else ((W.baseChange K).Ψ₂Sq).eval x₀) = 0 := by
    have h1 := congrArg (Polynomial.eval x₀) hΦdef
    rw [hΦ0] at h1
    simp only [eval_sub, eval_mul, eval_X, apply_ite (Polynomial.eval x₀), eval_one, hΨ0,
      mul_zero, zero_sub] at h1
    linear_combination h1
  rcases mul_eq_zero.mp h0 with h12 | hG
  · rcases mul_eq_zero.mp h12 with hE | hF
    ·
      have hb : ((W.baseChange K).ΨSq ((n : ℤ) + 1)).eval x₀ = 0 := by
        have h2 := ΨSq_eval_eq_zero_of_preΨ W (m := n + 1) (K := K)
          (by rwa [Nat.cast_add, Nat.cast_one])
        rwa [Nat.cast_add, Nat.cast_one] at h2
      exact eval_ne_of_isCoprime (isCoprime_ΨSq_succ W n) hΨ0 hb
    ·
      have hb : ((W.baseChange K).ΨSq ((n - 1 : ℕ) : ℤ)).eval x₀ = 0 :=
        ΨSq_eval_eq_zero_of_preΨ W (m := n - 1) (K := K)
          (by rwa [Nat.cast_sub hn, Nat.cast_one])
      have hA := isCoprime_ΨSq_succ W (K := K) (n - 1)
      have hc : ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by omega
      rw [hc] at hA
      exact eval_ne_of_isCoprime hA hb hΨ0
  ·
    by_cases hev : Even (n : ℤ)
    · rw [if_pos hev] at hG
      exact one_ne_zero hG
    · rw [if_neg hev] at hG
      have hnodd : ¬Even n := fun h => hev (by exact_mod_cast h)
      have hb : ((W.baseChange K).ΨSq ((n : ℤ) + 1)).eval x₀ = 0 := by
        have h2 : ((W.baseChange K).ΨSq ((n + 1 : ℕ) : ℤ)).eval x₀ = 0 := by
          rw [ΨSq_ofNat, if_pos (Nat.even_add_one.mpr hnodd), eval_mul, hG, mul_zero]
        rwa [Nat.cast_add, Nat.cast_one] at h2
      exact eval_ne_of_isCoprime (isCoprime_ΨSq_succ W n) hΨ0 hb

end Deep.Gen

end PortGenSmulFormula

section PortCardSurj

namespace Deep
namespace Gen

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

open scoped WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)

theorem nsmul_surjective_charfree [IsAlgClosed K] [W.IsElliptic] {n : ℕ} (hpos : 0 < n) :
    Function.Surjective (fun P : W.toAffine⟮K⟯ => n • P) := by
  intro Q
  rcases Q with _ | ⟨xQ, yQ, hQ⟩
  · refine ⟨0, ?_⟩
    show n • (0 : W.toAffine⟮K⟯) = Point.zero
    rw [nsmul_zero]
    exact Point.zero_def
  set F' := (W.baseChange K).Φ n with hFdef
  set G := (W.baseChange K).ΨSq n with hGdef
  have hFdeg : F'.natDegree = n ^ 2 := by
    have h := WeierstrassCurve.natDegree_Φ (W.baseChange K) (n : ℤ)
    rw [Int.natAbs_natCast] at h
    rw [hFdef, h]
  have hGdeg : G.natDegree ≤ n ^ 2 - 1 := by
    have h := WeierstrassCurve.natDegree_ΨSq_le (W.baseChange K) (n : ℤ)
    rw [Int.natAbs_natCast] at h
    rw [hGdef]; exact h
  have h1n : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hpos.ne')
  set p : K[X] := F' - C xQ * G with hpdef
  have hpdeg : p.natDegree = n ^ 2 := by
    rw [hpdef]
    rw [natDegree_sub_eq_left_of_natDegree_lt, hFdeg]
    refine lt_of_le_of_lt (natDegree_C_mul_le xQ G) ?_
    rw [hFdeg]
    omega
  have hpdegne : p.degree ≠ 0 := by
    have hpos' : 0 < p.natDegree := by rw [hpdeg]; omega
    exact (natDegree_pos_iff_degree_pos.mp hpos').ne'
  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root p hpdegne
  have hpx : p.eval x₀ = 0 := hx₀
  have hroot : F'.eval x₀ = xQ * G.eval x₀ := by
    rw [hpdef, eval_sub, eval_mul, eval_C, sub_eq_zero] at hpx
    exact hpx
  have hGx : G.eval x₀ ≠ 0 := by
    intro hG0
    have hF0 : F'.eval x₀ = 0 := by rw [hroot, hG0, mul_zero]
    obtain ⟨a, b, hab⟩ := isCoprime_Φ_ΨSq W (K := K) hpos
    rw [← hFdef, ← hGdef] at hab
    have h1 := congrArg (Polynomial.eval x₀) hab
    rw [eval_add, eval_mul, eval_mul, eval_one, hF0, hG0, mul_zero, mul_zero,
      add_zero] at h1
    exact zero_ne_one h1
  obtain ⟨y₀, hy₀⟩ : ∃ y : K, (W.baseChange K).toAffine.Equation x₀ y := by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
      (C 1 * X ^ 2 + C ((W.baseChange K).a₁ * x₀ + (W.baseChange K).a₃) * X
        + C (-(x₀ ^ 3 + (W.baseChange K).a₂ * x₀ ^ 2 + (W.baseChange K).a₄ * x₀ +
            (W.baseChange K).a₆)))
      (by rw [degree_quadratic one_ne_zero]; norm_num)
    refine ⟨y, ?_⟩
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X, one_mul] at hy
    linear_combination hy
  have h₀ : (W.baseChange K).toAffine.Nonsingular x₀ y₀ :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hy₀
  obtain ⟨x', y', h', hsmul, hx'⟩ := smul_x_eq W hpos h₀ hGx
  rw [← hFdef, ← hGdef] at hx'
  have hx'Q : x' = xQ := by
    rw [hroot] at hx'
    exact mul_right_cancel₀ hGx hx'
  subst hx'Q
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h'.1 hQ.1 rfl with rfl | rfl
  · exact ⟨Point.some x₀ y₀ h₀, hsmul⟩
  · have hnegQ : -(Point.some x' yQ hQ : W.toAffine⟮K⟯) =
        Point.some x' ((W.baseChange K).toAffine.negY x' yQ)
          ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr hQ) := Point.neg_some hQ
    have hprev : n • (Point.some x₀ y₀ h₀ : W.toAffine⟮K⟯) =
        -(Point.some x' yQ hQ) := by
      rw [hnegQ]
      exact hsmul
    have hsn : n • -(Point.some x₀ y₀ h₀ : W.toAffine⟮K⟯) =
        -(n • (Point.some x₀ y₀ h₀ : W.toAffine⟮K⟯)) :=
      neg_nsmul (Point.some x₀ y₀ h₀ : W.toAffine⟮K⟯) n
    refine ⟨-(Point.some x₀ y₀ h₀), ?_⟩
    show n • -(Point.some x₀ y₀ h₀ : W.toAffine⟮K⟯) = Point.some x' yQ hQ
    rw [hsn, hprev, neg_neg]

theorem exists_zsmul_eq [IsAlgClosed K] [W.IsElliptic] {n : ℤ} (hn : n ≠ 0)
    (P : W.toAffine⟮K⟯) : ∃ Q : W.toAffine⟮K⟯, n • Q = P := by
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  obtain ⟨Q, hQ⟩ := nsmul_surjective_charfree W (K := K) hpos P
  rcases Int.natAbs_eq n with h | h
  · exact ⟨Q, by rw [h, natCast_zsmul]; exact hQ⟩
  · exact ⟨-Q, by rw [h, neg_zsmul, zsmul_neg, neg_neg, natCast_zsmul]; exact hQ⟩

end Deep.Gen

theorem PortCard.exists_zsmul_eq_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    [DecidableEq K] (E : WeierstrassCurve K) [E.IsElliptic] {n : ℤ} (hn : n ≠ 0)
    (P : E.toAffine.Point) : ∃ Q : E.toAffine.Point, n • Q = P :=
  Deep.Gen.exists_zsmul_eq (F := K) (K := K) E hn P

end PortCardSurj

theorem solution {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (E : WeierstrassCurve K) [E.IsElliptic] {n : ℤ} (hn : n ≠ 0) (P : E.toAffine.Point) : ∃ Q : E.toAffine.Point, n • Q = P :=
  PortCard.exists_zsmul_eq_of_isAlgClosed E hn P
end FunctionFieldPullback.Exists


theorem WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (E : WeierstrassCurve K) [E.IsElliptic] {n : ℤ} (hn : n ≠ 0) (P : E.toAffine.Point) : ∃ Q : E.toAffine.Point, n • Q = P :=
  FunctionFieldPullback.Exists.solution E hn P

namespace FunctionFieldPullback.Good

open WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve
namespace Affine
namespace Good
open WeierstrassCurve.Affine WeierstrassCurve

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K] [IsAlgClosed K] [W.IsElliptic]

theorem not_forall_zsmul_eq_zero {n : ℤ} (hn : (n : K) ≠ 0) : ¬ ∀ S : (W⁄K).Point, n • S = 0 := by
  intro hall
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m ∨ n = -m := ⟨n.natAbs, Int.natAbs_eq n⟩
  have hmK : (m : K) ≠ 0 := by
    intro h0
    apply hn
    rcases hm with rfl | rfl
    · rw [Int.cast_natCast, h0]
    · rw [Int.cast_neg, Int.cast_natCast, h0, neg_zero]
  have hcard := WeierstrassCurve.card_torsion_of_isAlgClosed (K := K) W hmK
  have htop : Submodule.torsionBy ℤ (W⁄K).Point m = ⊤ := by
    rw [eq_top_iff]
    intro S _
    rw [Submodule.mem_torsionBy_iff]
    rcases hm with rfl | rfl
    · exact hall S
    · have := hall S
      rwa [neg_smul, neg_eq_zero] at this
  rw [htop, Nat.card_congr (Submodule.topEquiv (R := ℤ) (M := (W⁄K).Point)).toEquiv] at hcard
  have hm0 : m ≠ 0 := by rintro rfl; exact hmK Nat.cast_zero
  haveI : Finite (W⁄K).Point := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hm0)
  exact (infinite_point W K).not_finite ‹_›

end WeierstrassCurve.Affine.Good

open WeierstrassCurve.Affine.Good in
theorem solution {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K] [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] {n : ℤ} (hn : (n : K) ≠ 0) : WeierstrassCurve.Affine.MulGood W K n := by
  constructor
  · intro h0
    apply not_forall_zsmul_eq_zero W K hn
    intro S
    have := congrArg (Point.map (transPull W K S)) h0
    rw [map_zsmul, map_transPull_genericPoint, map_zero, smul_add, h0, zero_add, ← map_zsmul] at this
    exact Point.map_injective _ (this.trans (map_zero _).symm)
  · intro P hP
    apply not_forall_zsmul_eq_zero W K hn
    intro S
    have := congrArg (Point.map (transPull W K S)) hP
    rw [map_zsmul, map_transPull_genericPoint, Point.map_baseChange, smul_add, hP, ← map_zsmul,
      add_eq_left] at this
    exact Point.map_injective _ (this.trans (map_zero _).symm)
end FunctionFieldPullback.Good


theorem WeierstrassCurve.Affine.zsmul_genericPoint_good {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K] [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] {n : ℤ} (hn : (n : K) ≠ 0) : WeierstrassCurve.Affine.MulGood W K n :=
  FunctionFieldPullback.Good.solution W K hn

namespace FunctionFieldPullback.Finrank

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open Polynomial IntermediateField

theorem solution {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℤ} (hgood : MulGood W K n) : FiniteDimensional (mulPull W K n hgood).fieldRange (W⁄K).FunctionField ∧ Module.finrank (mulPull W K n hgood).fieldRange (W⁄K).FunctionField ≤ n.natAbs ^ 2 := by
  classical
  haveI hEK : (W⁄K).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  set L := (W⁄K).FunctionField with hL
  set gX := genericX W K with hXdef
  set gY := genericY W K with hYdef
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hgood.1 (zero_zsmul _)

  let f : K →ₐ[F] L := IsScalarTower.toAlgHom F K L
  have hf : (f : K →+* L) = algebraMap K L := rfl
  have hΦ : (W⁄L).Φ n = ((W⁄K).Φ n).map (algebraMap K L) := by
    rw [← hf]; exact W.baseChange_Φ f n
  have hΨSq : (W⁄L).ΨSq n = ((W⁄K).ΨSq n).map (algebraMap K L) := by
    rw [← hf]; exact W.baseChange_ΨSq f n
  have hΨ₂Sq : (W⁄L).Ψ₂Sq = (W⁄K).Ψ₂Sq.map (algebraMap K L) := by
    rw [← hf]; exact W.baseChange_Ψ₂Sq f

  have hγn : n • genericPoint W K ≠ 0 := hgood.1
  have hψ : ((W⁄L).ψ n).evalEval gX gY ≠ 0 := fun h0 =>
    hγn ((WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff (W⁄L) (generic_nonsingular W K) n).mpr h0)
  have hΨX : ((W⁄L).ΨSq n).eval gX ≠ 0 := by
    rw [← WeierstrassCurve.Affine.evalEval_psi_sq (W⁄L) (generic_equation W K) n]
    exact pow_ne_zero _ hψ

  obtain ⟨y', h', hmul⟩ :=
    WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div (W⁄L) (generic_nonsingular W K) hψ
  have hxn : mulPull W K n hgood gX = ((W⁄L).Φ n).eval gX / ((W⁄L).ΨSq n).eval gX := by
    rw [hXdef, mulPull_genericX' W K hgood]
    show (n • Point.some _ _ (generic_nonsingular W K)).xc = _
    rw [hmul, Point.xc_some]

  set A : L := (W⁄L).a₁ * gX + (W⁄L).a₃ with hA
  set B : L := -(gX ^ 3 + (W⁄L).a₂ * gX ^ 2 + (W⁄L).a₄ * gX + (W⁄L).a₆) with hB
  have hcoef : ∀ a : F, (algebraMap F L a) ∈ K⟮gX⟯ := fun a => by
    rw [IsScalarTower.algebraMap_apply F K L]
    exact IntermediateField.algebraMap_mem _ _
  have ha₁ : (W⁄L).a₁ = algebraMap F L W.a₁ := rfl
  have ha₂ : (W⁄L).a₂ = algebraMap F L W.a₂ := rfl
  have ha₃ : (W⁄L).a₃ = algebraMap F L W.a₃ := rfl
  have ha₄ : (W⁄L).a₄ = algebraMap F L W.a₄ := rfl
  have ha₆ : (W⁄L).a₆ = algebraMap F L W.a₆ := rfl
  have hXKX : gX ∈ K⟮gX⟯ := mem_adjoin_simple_self K gX
  have hAmem : A ∈ K⟮gX⟯ := by
    rw [hA, ha₁, ha₃]
    exact add_mem (mul_mem (hcoef _) hXKX) (hcoef _)
  have hBmem : B ∈ K⟮gX⟯ := by
    rw [hB, ha₂, ha₄, ha₆]
    refine neg_mem (add_mem (add_mem (add_mem (pow_mem hXKX 3) (mul_mem (hcoef _) (pow_mem hXKX 2)))
      (mul_mem (hcoef _) hXKX)) (hcoef _))
  have hYq : gY ^ 2 + A * gY + B = 0 := by
    have h := (equation_iff _ _).mp (generic_equation W K)
    rw [hA, hB]
    linear_combination h

  have hιX : (negEquiv W K : L →ₐ[K] L) gX = gX := negEquiv_genericX W K
  have hιY' : (negEquiv W K : L →ₐ[K] L) gY = -gY - A := by
    show negEquiv W K (genericY W K) = _
    rw [negEquiv_genericY, WeierstrassCurve.Affine.negY, hA]
    ring
  have hιY : ((negEquiv W K : L →ₐ[K] L) gY) ^ 2 + A * (negEquiv W K : L →ₐ[K] L) gY + B = 0 := by
    rw [hιY']
    linear_combination hYq
  have hιμ : (negEquiv W K : L →ₐ[K] L) (mulPull W K n hgood gY) ≠ mulPull W K n hgood gY := by
    intro heq
    change negEquiv W K (mulPull W K n hgood (genericY W K)) = mulPull W K n hgood (genericY W K) at heq
    rw [negEquiv_mulPull_genericY' W K hgood, mulPull_genericY' W K hgood] at heq

    have hP := Point.eq_some_xc_yc hγn
    have h2 : (2 : ℕ) • (n • genericPoint W K) = 0 := by
      rw [two_nsmul, add_eq_zero_iff_eq_neg]
      conv_rhs => rw [hP, Point.neg_some]
      conv_lhs => rw [hP]
      congr 1
      exact heq.symm
    rw [hP, WeierstrassCurve.Affine.Point.two_smul_some_eq_zero_iff (W⁄L), hΨ₂Sq,
      eval_map_algebraMap] at h2

    apply not_isIntegral_xc_of_ne_baseChange (n • genericPoint W K) hgood.1 hgood.2
    exact IsAlgebraic.isIntegral ⟨(W⁄K).Ψ₂Sq, WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic (W⁄K), h2⟩

  have hgen : IntermediateField.adjoin K {gX, gY} = ⊤ := FunctionField.adjoin_X_Y_eq_top (W⁄K)
  have key := IntermediateField.finrank_fieldRange_le_of_adjoin_pair_eq_top gX gY hgen A B hAmem hBmem hYq (mulPull W K n hgood)
    (negEquiv W K : L →ₐ[K] L) hιX hιY hιμ ((W⁄K).Φ n) ((W⁄K).ΨSq n)
    (d := n.natAbs ^ 2) (pow_pos (Int.natAbs_pos.mpr hn0) 2) ?_ ?_
  · exact key
  ·
    rw [← eval_map_algebraMap, ← eval_map_algebraMap, ← hΦ, ← hΨSq, hxn, div_mul_cancel₀ _ hΨX]
  · intro M c
    rw [← WeierstrassCurve.map_Φ, ← WeierstrassCurve.map_ΨSq]
    exact WeierstrassCurve.natDegree_Phi_sub_C_mul_PsiSq _ n c
end FunctionFieldPullback.Finrank


theorem WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℤ} (hgood : WeierstrassCurve.Affine.MulGood W K n) : FiniteDimensional (WeierstrassCurve.Affine.mulPull W K n hgood).fieldRange (W⁄K).FunctionField ∧ Module.finrank (WeierstrassCurve.Affine.mulPull W K n hgood).fieldRange (W⁄K).FunctionField ≤ n.natAbs ^ 2 :=
  FunctionFieldPullback.Finrank.solution W hgood

namespace FunctionFieldPullback.Main

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace WeilND

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]

lemma placeOf_congr {P Q : (W⁄K).Point} (hP : P ≠ 0) (hQ : Q ≠ 0) (h : P = Q) :
    placeOf W K P hP = placeOf W K Q hQ := by subst h; rfl

end WeilND

theorem solution {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hnK : (n : K) ≠ 0) (hpull : ∀ (hgood : MulGood W K (n : ℤ)) (P : (W⁄K).Point) (hP : P ≠ 0) (hnP : (n : ℤ) • P ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ), (placeOf W K ((n : ℤ) • P) hnP).valuation (W⁄K).FunctionField h ≤ WithZero.exp (-(k : ℤ)) → (placeOf W K P hP).valuation (W⁄K).FunctionField (mulPull W K n hgood h) ≤ WithZero.exp (-(k : ℤ))) {T : (W⁄K).Point} (g : (W⁄K).FunctionField) (hg : ∀ (P : (W⁄K).Point) (hP : P ≠ 0), (n : ℤ) • P ≠ 0 → (placeOf W K P hP).valuation (W⁄K).FunctionField g = if (n : ℤ) • P = T then WithZero.exp (-1) else 1) (hinv : ∀ S : (W⁄K).Point, (n : ℤ) • S = 0 → transEquiv W K S g = g) : T = 0 := by
  classical
  by_contra hT0
  have hn0 : (n : ℤ) ≠ 0 := by
    have : n ≠ 0 := fun h => hnK (by rw [h, Nat.cast_zero])
    exact_mod_cast this
  have hnK' : ((n : ℤ) : K) ≠ 0 := by exact_mod_cast hnK
  haveI hEK : (W⁄K).IsElliptic := by
    dsimp only [Affine.baseChange, WeierstrassCurve.baseChange]; infer_instance
  have hgood : MulGood W K (n : ℤ) := WeierstrassCurve.Affine.zsmul_genericPoint_good W K hnK'

  obtain ⟨hfd, hdeg⟩ := WeierstrassCurve.Affine.finrank_fieldRange_mulPull_le (K := K) W hgood
  rw [Int.natAbs_natCast] at hdeg
  haveI := hfd

  have hsurj : ∀ P : (W⁄K).Point, ∃ Q : (W⁄K).Point, (n : ℤ) • Q = P := fun P =>
    WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed (W⁄K) hn0 P

  let φ : Multiplicative (W⁄K).Point →* ((W⁄K).FunctionField ≃ₐ[K] (W⁄K).FunctionField) :=
    { toFun := fun S => transEquiv W K (Multiplicative.toAdd S)
      map_one' := by
        show transEquiv W K 0 = 1
        rw [transEquiv_zero]; rfl
      map_mul' := fun S S' => by
        show transEquiv W K (Multiplicative.toAdd S + Multiplicative.toAdd S') = _
        rw [transEquiv_add]; rfl }
  have hφ : Function.Injective φ := fun S S' h =>
    Multiplicative.toAdd.injective (transEquiv_injective W K h)
  let En : Subgroup (Multiplicative (W⁄K).Point) :=
    AddSubgroup.toSubgroup (Submodule.torsionBy ℤ (W⁄K).Point (n : ℤ)).toAddSubgroup
  have hmemEn : ∀ S, S ∈ En ↔ (n : ℤ) • Multiplicative.toAdd S = 0 := fun S => by
    show Multiplicative.toAdd S ∈ (Submodule.torsionBy ℤ (W⁄K).Point (n : ℤ)).toAddSubgroup ↔ _
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff]
  let H : Subgroup ((W⁄K).FunctionField ≃ₐ[K] (W⁄K).FunctionField) := En.map φ
  have hmemH : ∀ σ, σ ∈ H ↔ ∃ S : (W⁄K).Point, (n : ℤ) • S = 0 ∧ transEquiv W K S = σ := by
    intro σ
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨Multiplicative.toAdd S, (hmemEn S).mp hS, rfl⟩
    · rintro ⟨S, hS, rfl⟩
      exact ⟨Multiplicative.ofAdd S, (hmemEn _).mpr hS, rfl⟩

  have hcardEn : Nat.card En = n ^ 2 := by
    rw [← WeierstrassCurve.card_torsion_of_isAlgClosed W hnK]
    exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun S =>
      (hmemEn S).trans (Submodule.mem_torsionBy_iff (n : ℤ) (Multiplicative.toAdd S)).symm)
  have hcardH : Nat.card H = n ^ 2 := by
    rw [← hcardEn]
    exact Subgroup.card_map_of_injective hφ
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcardH]; exact pow_ne_zero _ (by exact_mod_cast hn0))
  haveI : Fintype H := Fintype.ofFinite H
  have hfix : Module.finrank (IntermediateField.fixedField H) (W⁄K).FunctionField = n ^ 2 := by
    rw [show Module.finrank (IntermediateField.fixedField H) (W⁄K).FunctionField =
        Module.finrank (FixedPoints.subfield H (W⁄K).FunctionField) (W⁄K).FunctionField from rfl,
      FixedPoints.finrank_eq_card, Fintype.card_eq_nat_card, hcardH]
  have hM : (mulPull W K (n : ℤ) hgood).fieldRange ≤ IntermediateField.fixedField H := by
    rintro x ⟨h, rfl⟩
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨S, hS, rfl⟩ := (hmemH σ).mp hσ
    exact transEquiv_mulPull' W K hgood hS h
  have hEq : (mulPull W K (n : ℤ) hgood).fieldRange = IntermediateField.fixedField H :=
    IntermediateField.eq_of_le_of_finrank_le' hM (by rw [hfix]; exact hdeg)
  have hgM : g ∈ (mulPull W K (n : ℤ) hgood).fieldRange := by
    rw [hEq, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    obtain ⟨S, hS, rfl⟩ := (hmemH σ).mp hσ
    exact hinv S hS
  obtain ⟨h, hh⟩ := hgM

  let pt : HeightOneSpectrum (W⁄K).CoordinateRing → (W⁄K).Point := fun v =>
    Classical.choose (placeOf_surjective W K v)
  have hpt0 : ∀ v, pt v ≠ 0 := fun v => Classical.choose (Classical.choose_spec (placeOf_surjective W K v))
  have hptv : ∀ v, placeOf W K (pt v) (hpt0 v) = v := fun v =>
    Classical.choose_spec (Classical.choose_spec (placeOf_surjective W K v))
  let N : HeightOneSpectrum (W⁄K).CoordinateRing → Option (HeightOneSpectrum (W⁄K).CoordinateRing) :=
    fun v => if hv : (n : ℤ) • pt v = 0 then none else Option.some (placeOf W K ((n : ℤ) • pt v) hv)
  have hNsome : ∀ v w, N v = Option.some w → ∃ hv : (n : ℤ) • pt v ≠ 0, placeOf W K ((n : ℤ) • pt v) hv = w := by
    intro v w hvw
    by_cases hv : (n : ℤ) • pt v = 0
    · simp only [N, hv, dite_true] at hvw; exact absurd hvw (by simp)
    · simp only [N, hv, dite_false, Option.some.injEq] at hvw
      exact ⟨hv, hvw⟩
  have hpt_of_place : ∀ {P : (W⁄K).Point} (hP : P ≠ 0), pt (placeOf W K P hP) = P := fun hP =>
    placeOf_injective W K _ _ (hptv _)
  have hN : ∀ w, ∃ v, N v = Option.some w := by
    intro w
    obtain ⟨U, hU, rfl⟩ := placeOf_surjective W K w
    obtain ⟨Q, hQ⟩ := hsurj U
    have hQ0 : Q ≠ 0 := by rintro rfl; exact hU (by rw [← hQ, smul_zero])
    refine ⟨placeOf W K Q hQ0, ?_⟩
    have hv : (n : ℤ) • pt (placeOf W K Q hQ0) ≠ 0 := by rw [hpt_of_place]; rwa [hQ]
    simp only [N, hv, dite_false, Option.some.injEq]
    exact WeilND.placeOf_congr W K _ _ (by rw [hpt_of_place, hQ])
  have key := IsDedekindDomain.HeightOneSpectrum.exists_eq_span_singleton_of_map_eq (R := (W⁄K).CoordinateRing) (K := (W⁄K).FunctionField)
    (mulPull W K (n : ℤ) hgood : (W⁄K).FunctionField →+* (W⁄K).FunctionField) N hN ?_ g (placeOf W K T hT0) ?_ ?_ ⟨h, hh⟩
  rotate_left
  ·
    intro v w hvw x k hx
    obtain ⟨hv, rfl⟩ := hNsome v w hvw
    rw [← hptv v]
    exact hpull hgood (pt v) (hpt0 v) hv x k hx
  ·
    intro v hv
    obtain ⟨hv', hw⟩ := hNsome v _ hv
    have hPT : (n : ℤ) • pt v = T := placeOf_injective W K _ _ hw
    rw [← hptv v, hg (pt v) (hpt0 v) hv', if_pos hPT]
  ·
    intro v w hvw hw
    obtain ⟨hv', rfl⟩ := hNsome v w hvw
    have hPT : (n : ℤ) • pt v ≠ T := fun h' => hw (WeilND.placeOf_congr W K _ _ h')
    rw [← hptv v, hg (pt v) (hpt0 v) hv', if_neg hPT]

  obtain ⟨r, hr⟩ := key
  have hr0 : r ≠ 0 := by
    intro h0
    apply (placeOf W K T hT0).ne_bot
    rw [hr, h0, Ideal.span_singleton_eq_bot]
  have hTs := Point.eq_some_xc_yc hT0
  have hcls : Point.toClass T = 0 := by
    rw [hTs, Point.toClass_some]
    exact (ClassGroup.mk_eq_one_of_coe_ideal (by rfl)).mpr ⟨r, hr0, hr⟩
  exact hT0 ((Point.toClass_eq_zero T).mp hcls)
end FunctionFieldPullback.Main


theorem WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hnK : (n : K) ≠ 0) (hpull : ∀ (hgood : WeierstrassCurve.Affine.MulGood W K (n : ℤ)) (P : (W⁄K).Point) (hP : P ≠ 0) (hnP : (n : ℤ) • P ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ), (WeierstrassCurve.Affine.placeOf W K ((n : ℤ) • P) hnP).valuation (W⁄K).FunctionField h ≤ WithZero.exp (-(k : ℤ)) → (WeierstrassCurve.Affine.placeOf W K P hP).valuation (W⁄K).FunctionField (WeierstrassCurve.Affine.mulPull W K n hgood h) ≤ WithZero.exp (-(k : ℤ))) {T : (W⁄K).Point} (g : (W⁄K).FunctionField) (hg : ∀ (P : (W⁄K).Point) (hP : P ≠ 0), (n : ℤ) • P ≠ 0 → (WeierstrassCurve.Affine.placeOf W K P hP).valuation (W⁄K).FunctionField g = if (n : ℤ) • P = T then WithZero.exp (-1) else 1) (hinv : ∀ S : (W⁄K).Point, (n : ℤ) • S = 0 → WeierstrassCurve.Affine.transEquiv W K S g = g) : T = 0 :=
  FunctionFieldPullback.Main.solution W hnK hpull g hg hinv

theorem WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq_of_pole {F K : Type*} [Field F]
    [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic]
    [IsDedekindDomain (W⁄K).CoordinateRing] {n : ℕ} (hnK : (n : K) ≠ 0)
    (hpull : ∀ (hgood : WeierstrassCurve.Affine.MulGood W K (n : ℤ)) (P : (W⁄K).Point) (hP : P ≠ 0)
      (hnP : (n : ℤ) • P ≠ 0) (h : (W⁄K).FunctionField) (k : ℕ),
      (WeierstrassCurve.Affine.placeOf W K ((n : ℤ) • P) hnP).valuation (W⁄K).FunctionField h ≤
          WithZero.exp (-(k : ℤ)) →
        (WeierstrassCurve.Affine.placeOf W K P hP).valuation (W⁄K).FunctionField
            (WeierstrassCurve.Affine.mulPull W K n hgood h) ≤ WithZero.exp (-(k : ℤ)))
    {T : (W⁄K).Point} (g : (W⁄K).FunctionField)
    (hg : ∀ (P : (W⁄K).Point) (hP : P ≠ 0), (n : ℤ) • P ≠ 0 →
      (WeierstrassCurve.Affine.placeOf W K P hP).valuation (W⁄K).FunctionField g =
        if (n : ℤ) • P = T then WithZero.exp 1 else 1)
    (hinv : ∀ S : (W⁄K).Point, (n : ℤ) • S = 0 → WeierstrassCurve.Affine.transEquiv W K S g = g) :
    T = 0 := by
  refine WeierstrassCurve.Affine.eq_zero_of_forall_transEquiv_eq W hnK hpull g⁻¹
    (fun P hP hnP => ?_) (fun S hS => ?_)
  · rw [map_inv₀, hg P hP hnP]
    split_ifs
    · exact (WithZero.exp_neg 1).symm
    · exact inv_one
  · rw [map_inv₀, hinv S hS]

end
