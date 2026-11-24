/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.RingTheory.Kaehler.Basic
public import MathlibExt.LinearAlgebra.ExteriorPowerSemilinear

/-!
# The algebraic de Rham differential

Let `A` be a commutative `R`-algebra and write `Ω^• = ⋀_A Ω[A⁄R]` for the exterior algebra of its
Kähler differentials. This file constructs the de Rham differential `d : Ω^• → Ω^•`
(`KaehlerDifferential.deRham`), the additive map with

* `d a = D a` for `a ∈ A = ⋀⁰` and `d (D b) = 0`;
* the graded Leibniz rule `d (x * y) = d x * y + σ x * d y`, where `σ` is the grade involution
  `CliffordAlgebra.involute` (`σ x = (-1)ⁿ x` on `⋀ⁿ`).

It raises degrees by one (`deRham_mem_exteriorPower`, `deRhamPow`), squares to zero
(`deRham_deRham`), and on generators it is
`d (a • D b₁ ∧ ⋯ ∧ D bₙ) = D a ∧ D b₁ ∧ ⋯ ∧ D bₙ` (`deRham_smul_ιMulti`). It commutes with the
maps induced by compatible ring maps (`mapₛₗ_deRham`), and it is linear over `p`-th powers when
`p = 0` in `A` (`deRham_pow_smul`).

## Construction

The grade involution makes `Ω^•` a bimodule over itself, with left action `x • y = σ x * y`. In
the trivial square-zero extension `Ω^• ⊕ Ω^•` by this bimodule, `a ↦ (a, D a)` is a central ring
homomorphism (`KaehlerDifferential.DeRham.scalar`), making the extension an `A`-algebra. The map
`b ↦ (D b, 0)` is an `R`-derivation for the resulting module structure, so it factors through
`Ω[A⁄R]`; its values square to zero, hence it extends to an `A`-algebra map `Ω^• → Ω^• ⊕ Ω^•`
whose first component is the identity. Its second component is `d`.

## References

* [Stacks Project, Section 10.132 (Tag 0FKF)](https://stacks.math.columbia.edu/tag/0FKF)
-/

@[expose] public noncomputable section

open ExteriorAlgebra

namespace ExteriorAlgebra

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- The grade involution negates the degree-one generators. -/
theorem involute_ι (m : M) : CliffordAlgebra.involute (ι A m) = -ι A m :=
  CliffordAlgebra.involute_ι m

/-- A degree-one element graded-commutes with every element: `v * x = σ x * v`. -/
theorem ι_mul_eq_involute_mul (v : M) (x : ExteriorAlgebra A M) :
    ι A v * x = CliffordAlgebra.involute x * ι A v := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact (Algebra.commutes r _).symm
  | ι m => rw [involute_ι, neg_mul, eq_neg_iff_add_eq_zero, ι_add_mul_swap]
  | mul x y hx hy => rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc, map_mul]
  | add x y hx hy => rw [mul_add, hx, hy, map_add, add_mul]

/-- The grade involution acts on `⋀ⁿ` by the sign `(-1)ⁿ`. -/
theorem involute_of_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra A M} (hx : x ∈ ⋀[A]^n M) :
    CliffordAlgebra.involute x = (-1 : A) ^ n • x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => rw [AlgHom.commutes, pow_zero, one_smul]
  | add x y i _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | mem_mul m hm i x _ ih =>
      obtain ⟨m₀, rfl⟩ := hm
      rw [map_mul, involute_ι, ih, neg_mul, mul_smul_comm, pow_succ, mul_neg_one, neg_smul]

/-- Elements of `⋀²` are fixed by the grade involution. -/
theorem involute_of_mem_exteriorPower_two {x : ExteriorAlgebra A M} (hx : x ∈ ⋀[A]^2 M) :
    CliffordAlgebra.involute x = x := by
  rw [involute_of_mem_exteriorPower hx, neg_one_sq, one_smul]

/-- Elements of `⋀²` commute with the degree-one generators. -/
theorem ι_mul_comm_of_mem_exteriorPower_two (v : M) {x : ExteriorAlgebra A M}
    (hx : x ∈ ⋀[A]^2 M) : ι A v * x = x * ι A v := by
  rw [ι_mul_eq_involute_mul, involute_of_mem_exteriorPower_two hx]

/-- The base change maps commute with the grade involutions. -/
theorem involute_mapₛₗ {S N : Type*} [CommRing S] [AddCommGroup N] [Module S N] (φ : A →+* S)
    (u : M →ₛₗ[φ] N) (x : ExteriorAlgebra A M) :
    CliffordAlgebra.involute (mapₛₗ φ u x) = mapₛₗ φ u (CliffordAlgebra.involute x) := by
  refine RingHom.congr_fun (ringHom_ext
    (f := (CliffordAlgebra.involute : ExteriorAlgebra S N →ₐ[S] _).toRingHom.comp (mapₛₗ φ u))
    (g := (mapₛₗ φ u).comp (CliffordAlgebra.involute : ExteriorAlgebra A M →ₐ[A] _).toRingHom)
    (fun r => ?_) (fun m => ?_)) x
  · simp
  · simp

end ExteriorAlgebra

namespace KaehlerDifferential

namespace DeRham

/-! ### The twisted square-zero extension -/

section Twisted

variable (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]

/-- The exterior algebra regarded as a bimodule over itself, with left action twisted by the grade
involution: `x • y = σ x * y` and `y <• x = y * x`. -/
def Twisted : Type _ := ExteriorAlgebra A M

instance : AddCommGroup (Twisted A M) := inferInstanceAs (AddCommGroup (ExteriorAlgebra A M))

variable {A M}

/-- An element of the exterior algebra, viewed in `Twisted`. -/
def Twisted.mk (x : ExteriorAlgebra A M) : Twisted A M := x

/-- The underlying element of the exterior algebra. -/
def Twisted.out (x : Twisted A M) : ExteriorAlgebra A M := x

@[simp] theorem Twisted.out_mk (x : ExteriorAlgebra A M) : (Twisted.mk x).out = x := rfl

@[simp] theorem Twisted.mk_out (x : Twisted A M) : Twisted.mk x.out = x := rfl

@[simp] theorem Twisted.out_zero : (0 : Twisted A M).out = 0 := rfl

@[simp] theorem Twisted.out_add (x y : Twisted A M) : (x + y).out = x.out + y.out := rfl

@[simp] theorem Twisted.out_neg (x : Twisted A M) : (-x).out = -x.out := rfl

@[simp] theorem Twisted.mk_zero : Twisted.mk (0 : ExteriorAlgebra A M) = 0 := rfl

theorem Twisted.out_injective : Function.Injective (Twisted.out : Twisted A M → _) :=
  fun _ _ h => h

instance : Module (ExteriorAlgebra A M) (Twisted A M) :=
  letI : Module (ExteriorAlgebra A M) (Twisted A M) :=
    inferInstanceAs (Module (ExteriorAlgebra A M) (ExteriorAlgebra A M))
  Module.compHom (Twisted A M)
    (CliffordAlgebra.involute : ExteriorAlgebra A M →ₐ[A] ExteriorAlgebra A M).toRingHom

instance : Module (ExteriorAlgebra A M)ᵐᵒᵖ (Twisted A M) :=
  inferInstanceAs (Module (ExteriorAlgebra A M)ᵐᵒᵖ (ExteriorAlgebra A M))

@[simp]
theorem Twisted.out_smul (x : ExteriorAlgebra A M) (y : Twisted A M) :
    (x • y).out = CliffordAlgebra.involute x * y.out := rfl

@[simp]
theorem Twisted.out_op_smul (x : (ExteriorAlgebra A M)ᵐᵒᵖ) (y : Twisted A M) :
    (x • y).out = y.out * x.unop := rfl

instance : SMulCommClass (ExteriorAlgebra A M) (ExteriorAlgebra A M)ᵐᵒᵖ (Twisted A M) where
  smul_comm x y z := Twisted.out_injective <| by
    simp only [Twisted.out_smul, Twisted.out_op_smul, mul_assoc]

variable (A M) in
/-- The trivial square-zero extension of `⋀ M` by the twisted bimodule. -/
abbrev Ext : Type _ := TrivSqZeroExt (ExteriorAlgebra A M) (Twisted A M)

@[simp]
theorem Ext.out_snd_mul (x y : Ext A M) :
    (x * y).snd.out = CliffordAlgebra.involute x.fst * y.snd.out + x.snd.out * y.fst := rfl

end Twisted

/-! ### The universal derivation into the extension -/

section Construction

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- The map `a ↦ (a, D a)` into the twisted square-zero extension. -/
def scalarFun (a : A) : Ext A Ω[A⁄R] :=
  TrivSqZeroExt.inl (algebraMap A _ a) +
    TrivSqZeroExt.inr (Twisted.mk (ι A (KaehlerDifferential.D R A a)))

@[simp]
theorem scalarFun_fst (a : A) : (scalarFun R A a).fst = algebraMap A _ a := by
  rw [scalarFun, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]

@[simp]
theorem scalarFun_snd_out (a : A) :
    (scalarFun R A a).snd.out = ι A (KaehlerDifferential.D R A a) := by
  rw [scalarFun, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
    Twisted.out_mk]

/-- The ring homomorphism `a ↦ (a, D a)` into the twisted square-zero extension. -/
def scalar : A →+* Ext A Ω[A⁄R] where
  toFun := scalarFun R A
  map_one' := by
    refine TrivSqZeroExt.ext ?_ (Twisted.out_injective ?_)
    · rw [scalarFun_fst, map_one, TrivSqZeroExt.fst_one]
    · rw [scalarFun_snd_out, Derivation.map_one_eq_zero, map_zero, TrivSqZeroExt.snd_one,
        Twisted.out_zero]
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ (Twisted.out_injective ?_)
    · rw [TrivSqZeroExt.fst_mul, scalarFun_fst, scalarFun_fst, scalarFun_fst, map_mul]
    · rw [Ext.out_snd_mul, scalarFun_fst, scalarFun_fst, scalarFun_snd_out, scalarFun_snd_out,
        scalarFun_snd_out, AlgHom.commutes, Derivation.leibniz, map_add, map_smul, map_smul,
        Algebra.smul_def, Algebra.smul_def, ← Algebra.commutes b, add_comm]
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ (Twisted.out_injective ?_)
    · rw [scalarFun_fst, map_zero, TrivSqZeroExt.fst_zero]
    · rw [scalarFun_snd_out, map_zero, map_zero, TrivSqZeroExt.snd_zero, Twisted.out_zero]
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ (Twisted.out_injective ?_)
    · rw [TrivSqZeroExt.fst_add, scalarFun_fst, scalarFun_fst, scalarFun_fst, map_add]
    · rw [TrivSqZeroExt.snd_add, Twisted.out_add, scalarFun_snd_out, scalarFun_snd_out,
        scalarFun_snd_out, map_add, map_add]

@[simp]
theorem scalar_fst (a : A) : (scalar R A a).fst = algebraMap A _ a := scalarFun_fst R A a

@[simp]
theorem scalar_snd_out (a : A) : (scalar R A a).snd.out = ι A (KaehlerDifferential.D R A a) :=
  scalarFun_snd_out R A a

theorem scalar_commutes (a : A) (t : Ext A Ω[A⁄R]) : scalar R A a * t = t * scalar R A a := by
  refine TrivSqZeroExt.ext (by simp [Algebra.commutes]) (Twisted.out_injective ?_)
  simp only [Ext.out_snd_mul, scalar_fst, scalar_snd_out, AlgHom.commutes]
  rw [Algebra.commutes, ι_mul_eq_involute_mul, add_comm]

/-- The `A`-algebra structure on the extension given by `scalar`. -/
abbrev algebraExt : Algebra A (Ext A Ω[A⁄R]) := (scalar R A).toAlgebra' (scalar_commutes R A)

/-- The `R`-algebra structure on the extension given by `scalar`. -/
abbrev algebraExtBase : Algebra R (Ext A Ω[A⁄R]) :=
  ((scalar R A).comp (algebraMap R A)).toAlgebra' fun _ t => scalar_commutes R A _ t

attribute [local instance] algebraExt algebraExtBase

theorem algebraMap_ext (a : A) : algebraMap A (Ext A Ω[A⁄R]) a = scalar R A a := rfl

theorem smul_ext (a : A) (t : Ext A Ω[A⁄R]) : a • t = scalar R A a * t := rfl

theorem smul_ext_base (r : R) (t : Ext A Ω[A⁄R]) : r • t = scalar R A (algebraMap R A r) * t :=
  rfl

theorem isScalarTower_ext : IsScalarTower R A (Ext A Ω[A⁄R]) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] isScalarTower_ext

theorem scalar_mul_inl (a : A) (x : ExteriorAlgebra A Ω[A⁄R]) :
    scalar R A a * TrivSqZeroExt.inl x = TrivSqZeroExt.inl (algebraMap A _ a * x) +
      TrivSqZeroExt.inr (Twisted.mk (ι A (KaehlerDifferential.D R A a) * x)) := by
  refine TrivSqZeroExt.ext ?_ (Twisted.out_injective ?_)
  · rw [TrivSqZeroExt.fst_mul, scalar_fst, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
  · rw [Ext.out_snd_mul, scalar_fst, scalar_snd_out, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, Twisted.out_zero,
      mul_zero, zero_add, zero_add, Twisted.out_mk]

/-- The `R`-linear map `b ↦ (D b, 0)` into the twisted extension. -/
def derivationLinear : A →ₗ[R] Ext A Ω[A⁄R] where
  toFun b := TrivSqZeroExt.inl (ι A (KaehlerDifferential.D R A b))
  map_add' b c := by rw [map_add, map_add, TrivSqZeroExt.inl_add]
  map_smul' r b := by
    rw [RingHom.id_apply, smul_ext_base, scalar_mul_inl, Algebra.smul_def, Derivation.leibniz,
      Derivation.map_algebraMap, smul_zero, add_zero, map_smul, Algebra.smul_def, map_zero,
      zero_mul, Twisted.mk_zero, TrivSqZeroExt.inr_zero, add_zero]

theorem derivationLinear_apply (b : A) :
    derivationLinear R A b = TrivSqZeroExt.inl (ι A (KaehlerDifferential.D R A b)) := rfl

/-- The derivation `b ↦ (D b, 0)` into the twisted extension. -/
def derivation : Derivation R A (Ext A Ω[A⁄R]) :=
  Derivation.mk' (derivationLinear R A) fun a b => by
    rw [derivationLinear_apply, derivationLinear_apply, derivationLinear_apply, smul_ext,
      smul_ext, scalar_mul_inl, scalar_mul_inl, Derivation.leibniz, map_add, map_smul, map_smul,
      Algebra.smul_def, Algebra.smul_def]
    refine TrivSqZeroExt.ext ?_ (Twisted.out_injective ?_)
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
        Twisted.out_add, Twisted.out_zero, Twisted.out_mk, zero_add]
      rw [ι_add_mul_swap]

theorem derivation_apply (b : A) :
    derivation R A b = TrivSqZeroExt.inl (ι A (KaehlerDifferential.D R A b)) := rfl

/-- The linear map `Ω[A⁄R] → Ext` induced by `derivation`. -/
def lift : Ω[A⁄R] →ₗ[A] Ext A Ω[A⁄R] := (derivation R A).liftKaehlerDifferential

@[simp]
theorem lift_D (b : A) :
    lift R A (KaehlerDifferential.D R A b) =
      TrivSqZeroExt.inl (ι A (KaehlerDifferential.D R A b)) :=
  ((derivation R A).liftKaehlerDifferential_comp_D b).trans (derivation_apply R A b)

/-- An induction principle for Kähler differentials: a property closed under sums and scalar
multiples which holds on the image of `D` holds everywhere. -/
theorem induction_D {P : Ω[A⁄R] → Prop} (D : ∀ b, P (KaehlerDifferential.D R A b))
    (zero : P 0) (add : ∀ x y, P x → P y → P (x + y)) (smul : ∀ (a : A) x, P x → P (a • x))
    (ω : Ω[A⁄R]) : P ω := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem y hy => obtain ⟨b, rfl⟩ := hy; exact D b
  | zero => exact zero
  | add y z _ _ hy hz => exact add y z hy hz
  | smul a y _ hy => exact smul a y hy

theorem lift_fst (ω : Ω[A⁄R]) : (lift R A ω).fst = ι A ω := by
  induction ω using induction_D R A with
  | D b => simp
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul a x hx => rw [map_smul, smul_ext, TrivSqZeroExt.fst_mul, hx, scalar_fst, map_smul,
      Algebra.smul_def]

theorem lift_snd_mem (ω : Ω[A⁄R]) : (lift R A ω).snd.out ∈ ⋀[A]^2 Ω[A⁄R] := by
  induction ω using induction_D R A with
  | D b => simp
  | zero => simp
  | add x y hx hy => simpa using Submodule.add_mem _ hx hy
  | smul a x hx =>
      rw [map_smul, smul_ext, Ext.out_snd_mul, scalar_fst, scalar_snd_out, AlgHom.commutes,
        lift_fst, ← Algebra.smul_def]
      exact Submodule.add_mem _ (Submodule.smul_mem _ a hx)
        (mul_mem_exteriorPower (ι_mem_exteriorPower _) (ι_mem_exteriorPower _))

theorem lift_mul_self (ω : Ω[A⁄R]) : lift R A ω * lift R A ω = 0 := by
  refine TrivSqZeroExt.ext ?_ (Twisted.out_injective ?_)
  · rw [TrivSqZeroExt.fst_mul, lift_fst, ι_sq_zero, TrivSqZeroExt.fst_zero]
  · rw [Ext.out_snd_mul, lift_fst, involute_ι, neg_mul,
      ← ι_mul_comm_of_mem_exteriorPower_two ω (lift_snd_mem R A ω), neg_add_cancel,
      TrivSqZeroExt.snd_zero, Twisted.out_zero]

/-- The `A`-algebra map `Ω^• → Ext` extending `lift`. -/
def toExt : ExteriorAlgebra A Ω[A⁄R] →ₐ[A] Ext A Ω[A⁄R] :=
  ExteriorAlgebra.lift A ⟨lift R A, lift_mul_self R A⟩

@[simp]
theorem toExt_ι (ω : Ω[A⁄R]) : toExt R A (ι A ω) = lift R A ω :=
  ExteriorAlgebra.lift_ι_apply A _ _ ω

@[simp]
theorem toExt_algebraMap (a : A) : toExt R A (algebraMap A _ a) = scalar R A a :=
  ((toExt R A).commutes a).trans (algebraMap_ext R A a)

@[simp]
theorem toExt_fst (x : ExteriorAlgebra A Ω[A⁄R]) : (toExt R A x).fst = x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => rw [toExt_algebraMap, scalar_fst]
  | ι ω => rw [toExt_ι, lift_fst]
  | mul x y hx hy => rw [map_mul, TrivSqZeroExt.fst_mul, hx, hy]
  | add x y hx hy => rw [map_add, TrivSqZeroExt.fst_add, hx, hy]

end Construction

end DeRham

open DeRham

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-! ### The de Rham differential -/

/-- **The de Rham differential** `d : Ω^•_{A/R} → Ω^•_{A/R}` on the exterior algebra of the
Kähler differentials: the additive map with `d a = D a` on `A`, `d (D b) = 0` and
`d (x * y) = d x * y + σ x * d y`. -/
def deRham : ExteriorAlgebra A Ω[A⁄R] →+ ExteriorAlgebra A Ω[A⁄R] where
  toFun x := (toExt R A x).snd.out
  map_zero' := by rw [map_zero, TrivSqZeroExt.snd_zero, Twisted.out_zero]
  map_add' x y := by rw [map_add, TrivSqZeroExt.snd_add, Twisted.out_add]

variable {R A}

theorem deRham_apply (x : ExteriorAlgebra A Ω[A⁄R]) : deRham R A x = (toExt R A x).snd.out := rfl

/-- The graded Leibniz rule. -/
theorem deRham_mul (x y : ExteriorAlgebra A Ω[A⁄R]) :
    deRham R A (x * y) = deRham R A x * y + CliffordAlgebra.involute x * deRham R A y := by
  rw [deRham_apply, map_mul, Ext.out_snd_mul, toExt_fst, toExt_fst, deRham_apply, deRham_apply,
    add_comm]

/-- On `A = ⋀⁰`, the de Rham differential is the universal derivation. -/
@[simp]
theorem deRham_algebraMap (a : A) :
    deRham R A (algebraMap A _ a) = ι A (KaehlerDifferential.D R A a) := by
  rw [deRham_apply, toExt_algebraMap, scalar_snd_out]

@[simp]
theorem deRham_one : deRham R A 1 = 0 := by
  rw [← map_one (algebraMap A (ExteriorAlgebra A Ω[A⁄R])), deRham_algebraMap,
    Derivation.map_one_eq_zero, map_zero]

/-- The exact one-forms `D b` are closed. -/
@[simp]
theorem deRham_ι_D (b : A) : deRham R A (ι A (KaehlerDifferential.D R A b)) = 0 := by
  rw [deRham_apply, toExt_ι, lift_D, TrivSqZeroExt.snd_inl, Twisted.out_zero]

theorem deRham_ι_mem (ω : Ω[A⁄R]) : deRham R A (ι A ω) ∈ ⋀[A]^2 Ω[A⁄R] := by
  rw [deRham_apply, toExt_ι]
  exact lift_snd_mem R A ω

theorem deRham_algebraMap_mul (a : A) (x : ExteriorAlgebra A Ω[A⁄R]) :
    deRham R A (algebraMap A _ a * x) =
      ι A (KaehlerDifferential.D R A a) * x + algebraMap A _ a * deRham R A x := by
  rw [deRham_mul, deRham_algebraMap, AlgHom.commutes]

theorem deRham_smul (a : A) (x : ExteriorAlgebra A Ω[A⁄R]) :
    deRham R A (a • x) = ι A (KaehlerDifferential.D R A a) * x + a • deRham R A x := by
  rw [Algebra.smul_def, deRham_algebraMap_mul, Algebra.smul_def]

/-- The de Rham differential is `R`-linear. -/
theorem deRham_algebraMap_smul (r : R) (x : ExteriorAlgebra A Ω[A⁄R]) :
    deRham R A (algebraMap R A r • x) = algebraMap R A r • deRham R A x := by
  rw [deRham_smul, Derivation.map_algebraMap, map_zero, zero_mul, zero_add]

/-- The de Rham differential raises degrees by one. -/
theorem deRham_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra A Ω[A⁄R]}
    (hx : x ∈ ⋀[A]^n Ω[A⁄R]) : deRham R A x ∈ ⋀[A]^(n + 1) Ω[A⁄R] := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap a => rw [deRham_algebraMap]; exact ι_mem_exteriorPower _
  | add x y i _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | mem_mul m hm i x hx ih =>
      obtain ⟨ω, rfl⟩ := hm
      rw [deRham_mul, involute_ι, neg_mul]
      refine Submodule.add_mem _ ?_ (Submodule.neg_mem _ ?_)
      · have := mul_mem_exteriorPower (deRham_ι_mem (R := R) ω) hx
        rwa [show 2 + i = i + 1 + 1 by omega] at this
      · have := mul_mem_exteriorPower (ι_mem_exteriorPower ω) ih
        rwa [show 1 + (i + 1) = i + 1 + 1 by omega] at this

/-- The de Rham differential is odd: it anticommutes with the grade involution. -/
theorem involute_deRham (x : ExteriorAlgebra A Ω[A⁄R]) :
    CliffordAlgebra.involute (deRham R A x) = -deRham R A (CliffordAlgebra.involute x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => rw [deRham_algebraMap, involute_ι, AlgHom.commutes, deRham_algebraMap]
  | ι ω =>
      rw [involute_of_mem_exteriorPower_two (deRham_ι_mem ω), involute_ι, map_neg, neg_neg]
  | mul x y hx hy =>
      rw [deRham_mul, map_add, map_mul, map_mul, hx, map_mul, hy, CliffordAlgebra.involute_involute,
        deRham_mul, CliffordAlgebra.involute_involute, neg_add, neg_mul, mul_neg]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, neg_add]

theorem deRham_deRham_mul (x y : ExteriorAlgebra A Ω[A⁄R]) :
    deRham R A (deRham R A (x * y)) =
      deRham R A (deRham R A x) * y + x * deRham R A (deRham R A y) := by
  rw [deRham_mul, map_add, deRham_mul, deRham_mul, involute_deRham,
    CliffordAlgebra.involute_involute, neg_mul]
  abel

/-- The de Rham differential squares to zero. -/
@[simp]
theorem deRham_deRham (x : ExteriorAlgebra A Ω[A⁄R]) : deRham R A (deRham R A x) = 0 := by
  have hι : ∀ ω : Ω[A⁄R], deRham R A (deRham R A (ι A ω)) = 0 := by
    intro ω
    induction ω using DeRham.induction_D R A with
    | D b => rw [deRham_ι_D, map_zero]
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, add_zero]
    | smul a x hx =>
        rw [map_smul, Algebra.smul_def, deRham_deRham_mul, hx, mul_zero, add_zero,
          deRham_algebraMap, deRham_ι_D, zero_mul]
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => rw [deRham_algebraMap, deRham_ι_D]
  | ι ω => exact hι ω
  | mul x y hx hy => rw [deRham_deRham_mul, hx, hy, zero_mul, mul_zero, add_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- Wedges of exact one-forms are closed. -/
@[simp]
theorem deRham_ιMulti_D (n : ℕ) (b : Fin n → A) :
    deRham R A (ExteriorAlgebra.ιMulti A n fun i => KaehlerDifferential.D R A (b i)) = 0 := by
  induction n with
  | zero => rw [ιMulti_zero_apply, deRham_one]
  | succ n ih =>
      rw [ιMulti_succ_apply, deRham_mul, deRham_ι_D, zero_mul, zero_add,
        show Matrix.vecTail (fun i => KaehlerDifferential.D R A (b i)) =
          fun i => KaehlerDifferential.D R A (b i.succ) from rfl, ih, mul_zero]

/-- **The de Rham formula on generators**:
`d (a • D b₀ ∧ ⋯ ∧ D bₙ₋₁) = D a ∧ D b₀ ∧ ⋯ ∧ D bₙ₋₁`. -/
theorem deRham_smul_ιMulti (n : ℕ) (a : A) (b : Fin n → A) :
    deRham R A (a • ExteriorAlgebra.ιMulti A n fun i => KaehlerDifferential.D R A (b i)) =
      ExteriorAlgebra.ιMulti A (n + 1) fun i =>
        KaehlerDifferential.D R A ((Fin.cons a b : Fin (n + 1) → A) i) := by
  rw [deRham_smul, deRham_ιMulti_D, smul_zero, add_zero, ιMulti_succ_apply]
  rfl

/-- In characteristic `p` the de Rham differential is linear over `p`-th powers. -/
theorem deRham_pow_smul (p : ℕ) (hp : (p : A) = 0) (a : A) (x : ExteriorAlgebra A Ω[A⁄R]) :
    deRham R A (a ^ p • x) = a ^ p • deRham R A x := by
  rw [deRham_smul, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul A, hp, zero_smul, map_zero,
    zero_mul, zero_add]

/-- The de Rham differential commutes with the maps induced by a ring homomorphism `φ` and a
`φ`-semilinear map of differentials carrying `D a` to `D (φ a)`. -/
theorem mapₛₗ_deRham {R' B : Type*} [CommRing R'] [CommRing B] [Algebra R' B] (φ : A →+* B)
    (u : Ω[A⁄R] →ₛₗ[φ] Ω[B⁄R'])
    (hu : ∀ a, u (KaehlerDifferential.D R A a) = KaehlerDifferential.D R' B (φ a))
    (x : ExteriorAlgebra A Ω[A⁄R]) :
    mapₛₗ φ u (deRham R A x) = deRham R' B (mapₛₗ φ u x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap a => rw [deRham_algebraMap, mapₛₗ_ι, hu, mapₛₗ_algebraMap, deRham_algebraMap]
  | ι ω =>
      induction ω using DeRham.induction_D R A with
      | D b => rw [deRham_ι_D, map_zero, mapₛₗ_ι, hu, deRham_ι_D]
      | zero => simp
      | add _ _ hx hy => simp only [map_add, hx, hy]
      | smul a x hx =>
          rw [map_smul, Algebra.smul_def, deRham_algebraMap_mul, map_add, map_mul, map_mul,
            mapₛₗ_ι, hu, mapₛₗ_algebraMap, hx, map_mul, mapₛₗ_algebraMap, deRham_algebraMap_mul]
  | mul x y hx hy =>
      rw [deRham_mul, map_add, map_mul, map_mul, hx, hy, ← involute_mapₛₗ, map_mul, deRham_mul]
  | add _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- Additive maps out of `⋀ⁿ Ω[A⁄R]` agreeing on the generators `a • D b₁ ∧ ⋯ ∧ D bₙ` are equal:
these generators span `⋀ⁿ Ω[A⁄R]` additively. -/
theorem addMonoidHom_ext_ιMulti {N : Type*} [AddCommGroup N] {n : ℕ}
    {f g : ⋀[A]^n Ω[A⁄R] →+ N}
    (h : ∀ (a : A) (b : Fin n → A),
      f (a • exteriorPower.ιMulti A n fun i => KaehlerDifferential.D R A (b i)) =
        g (a • exteriorPower.ιMulti A n fun i => KaehlerDifferential.D R A (b i))) :
    f = g := by
  ext x
  have key : ∀ y ∈ Submodule.span A (exteriorPower.ιMulti A n ''
      {b | Set.range b ⊆ Set.range (KaehlerDifferential.D R A)}),
      ∀ c : A, f (c • y) = g (c • y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨b, hb, rfl⟩ := hy
        intro c
        choose e he using fun j => hb (Set.mem_range_self j)
        obtain rfl : b = fun j => KaehlerDifferential.D R A (e j) := funext fun j => (he j).symm
        exact h c e
    | zero => intro c; rw [smul_zero, map_zero, map_zero]
    | add y z _ _ hy hz => intro c; rw [smul_add, map_add, map_add, hy, hz]
    | smul a y _ hy => intro c; rw [smul_smul]; exact hy (c * a)
  have hx := key x (by
    rw [exteriorPower.ιMulti_span_of_span (R := A) (n := n) (M := Ω[A⁄R])
      (KaehlerDifferential.span_range_derivation R A)]
    trivial) 1
  rwa [one_smul] at hx

/-- The de Rham differential `⋀ⁿ Ω[A⁄R] → ⋀ⁿ⁺¹ Ω[A⁄R]` in degree `n`. -/
def deRhamPow (n : ℕ) : ⋀[A]^n Ω[A⁄R] →+ ⋀[A]^(n + 1) Ω[A⁄R] where
  toFun x := ⟨deRham R A x, deRham_mem_exteriorPower x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

variable (R A) in
@[simp]
theorem coe_deRhamPow (n : ℕ) (x : ⋀[A]^n Ω[A⁄R]) :
    (deRhamPow (R := R) n x : ExteriorAlgebra A Ω[A⁄R]) = deRham R A x := rfl

end KaehlerDifferential
