/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBar
public import Mathlib.Algebra.Azumaya.Defs
public import MathlibExt.Algebra.Homology.Hochschild.OuterWord
public import MathlibExt.Algebra.Module.TensorPowerOuterAction
public import Mathlib.Algebra.Module.ULift

/-!
# The bar complex as an enveloping-module complex

Let k be a commutative ring and A an associative unital k-algebra.
The enveloping algebra E = A ⊗[k] Aᵐᵒᵖ acts on the bar term
P_n = A ⊗[k] A^{⊗(n+1)} by multiplying the first factor on the left
and the last factor on the right:
(u ⊗ vᵐᵒᵖ) • (a_0 ⊗ ⋯ ⊗ a_{n+1}) =
u a_0 ⊗ a_1 ⊗ ⋯ ⊗ a_{n+1} v.

Every adjacent face is E-linear, so the alternating adjacent-product
differential defines a chain complex of left E-modules. Multiplication
P_0 → A is E-linear for the regular action (u ⊗ vᵐᵒᵖ) • a = uav
and annihilates d_1. For k : Type u and A : Type v, the complex
and its lifted regular augmentation target lie in universe max{u,v}.

Reference: J.-L. Loday, Cyclic Homology, §1.1.
-/
@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open ModuleCat.Algebra.Hochschild
open scoped TensorProduct

universe u v
namespace ModuleCat.Algebra.Hochschild.AdjacentBar

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
The enveloping algebra is the tensor product with the opposite right
factor. Its multiplication on elementary tensors is
(a ⊗ bᵐᵒᵖ)(c ⊗ dᵐᵒᵖ) = ac ⊗ (db)ᵐᵒᵖ. -/
abbrev EnvelopingAlgebra := A ⊗[k] Aᵐᵒᵖ

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
The regular representation E → End_k(A) sends a ⊗ bᵐᵒᵖ to
the operator x ↦ axb. -/
abbrev regularEnvelopingAction : EnvelopingAlgebra k A →ₐ[k] Module.End k A :=
  AlgHom.mulLeftRight k A

private def barPure (n : ℕ) (a : Fin (n + 2) → A) : A ⊗[k] TensorPower k (n + 1) A :=
  a 0 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.tail a)

private theorem representation_barPure (n : ℕ) (l r : A) (a : Fin (n + 2) → A) :
    TensorPower.outerRepresentation k A n (l ⊗ₜ[k] MulOpposite.op r) (barPure k A n a) =
      barPure k A n (outerWord n l r a) := by
  have h := TensorPower.outerModule_tprod k A n l r (a 0) (Fin.tail a)
  change TensorPower.outerRepresentation k A n (l ⊗ₜ[k] MulOpposite.op r)
    (a 0 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.tail a)) = _ at h
  have hlast : (Fin.tail a) (Fin.last n) = a (Fin.last (n + 1)) := rfl
  simpa only [barPure, outerWord, Fin.cons_zero, Fin.tail_cons, hlast] using h

private theorem adjacentFace_barPure (n : ℕ) (i : Fin (n + 2)) (a : Fin (n + 3) → A) :
    (NonUnital.regularFace k A (n + 1) i.castSucc).hom (barPure k A (n + 1) a) =
      barPure k A n (hochschildMulAdjacent i a) := by
  apply (TensorPower.consEquiv k A (n + 1)).injective
  have h := NonUnital.regularFace_cons_tprod k A (n + 1) i (a 0) (Fin.tail a)
  simpa only [barPure, TensorPower.consEquiv_tmul, Fin.cons_self_tail] using h

private theorem adjacentFace_pure_intertwines (n : ℕ) (i : Fin (n + 2)) (l r : A)
    (a : Fin (n + 3) → A) :
    (NonUnital.regularFace k A (n + 1) i.castSucc).hom
        (TensorPower.outerRepresentation k A (n + 1)
          (l ⊗ₜ[k] MulOpposite.op r) (barPure k A (n + 1) a)) =
      TensorPower.outerRepresentation k A n (l ⊗ₜ[k] MulOpposite.op r)
        ((NonUnital.regularFace k A (n + 1) i.castSucc).hom (barPure k A (n + 1) a)) := by
  let f := (NonUnital.regularFace k A (n + 1) i.castSucc).hom
  calc
    f (TensorPower.outerRepresentation k A (n + 1)
        (l ⊗ₜ[k] MulOpposite.op r) (barPure k A (n + 1) a)) =
        f (barPure k A (n + 1) (outerWord (n + 1) l r a)) :=
      congrArg f (representation_barPure k A (n + 1) l r a)
    _ = barPure k A n (hochschildMulAdjacent i (outerWord (n + 1) l r a)) :=
      adjacentFace_barPure k A n i _
    _ = barPure k A n (outerWord n l r (hochschildMulAdjacent i a)) :=
      congrArg (barPure k A n) (mulAdjacent_outerWord n i l r a)
    _ = TensorPower.outerRepresentation k A n (l ⊗ₜ[k] MulOpposite.op r)
        (barPure k A n (hochschildMulAdjacent i a)) :=
      (representation_barPure k A n l r _).symm
    _ = TensorPower.outerRepresentation k A n (l ⊗ₜ[k] MulOpposite.op r)
        (f (barPure k A (n + 1) a)) :=
      congrArg (TensorPower.outerRepresentation k A n (l ⊗ₜ[k] MulOpposite.op r))
        (adjacentFace_barPure k A n i a).symm

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
On P_n = A ⊗[k] A^{⊗(n+1)}, E acts on the two outer
factors. Each adjacent face δ_i : P_{n+1} → P_n satisfies
δ_i(z • x) = z • δ_i(x), for z ∈ E and 0 ≤ i ≤ n+1. -/
theorem barAdjacentFace_intertwines (n : ℕ) (i : Fin (n + 2)) (z : EnvelopingAlgebra k A) :
    (NonUnital.regularFace k A (n + 1) i.castSucc).hom.comp
        (TensorPower.outerRepresentation k A (n + 1) z) =
      (TensorPower.outerRepresentation k A n z).comp
        (NonUnital.regularFace k A (n + 1) i.castSucc).hom := by
  let f : (A ⊗[k] TensorPower k (n + 2) A) →ₗ[k]
      A ⊗[k] TensorPower k (n + 1) A :=
    (NonUnital.regularFace k A (n + 1) i.castSucc).hom
  induction z using TensorProduct.inductionOn with
  | tmul l r =>
      apply tensorPower_ext
        (f := f.comp (TensorPower.outerRepresentation k A (n + 1) (l ⊗ₜ[k] r)))
        (g := (TensorPower.outerRepresentation k A n (l ⊗ₜ[k] r)).comp f)
      intro a₀ a
      have hp := adjacentFace_pure_intertwines k A n i l r.unop (Fin.cons a₀ a)
      simpa only [LinearMap.comp_apply, barPure, Fin.cons_zero, Fin.tail_cons,
        MulOpposite.op_unop, f] using hp
  | add z w hz hw =>
      apply LinearMap.ext
      intro x
      simpa only [map_add, LinearMap.add_apply, LinearMap.comp_apply] using
        congrArg₂ (· + ·) (DFunLike.congr_fun hz x) (DFunLike.congr_fun hw x)

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
The adjacent-product bar boundary d_{n+1} : P_{n+1} → P_n
commutes with the outer E-action: d_{n+1}(z • x) = z • d_{n+1}(x).
Its signs are (−1)^i on the i-th adjacent multiplication. -/
theorem underlyingBarBoundary_intertwines (n : ℕ) (z : EnvelopingAlgebra k A) :
    ((underlyingBar k A).d (n + 1) n).hom.comp
        (TensorPower.outerRepresentation k A (n + 1) z) =
      (TensorPower.outerRepresentation k A n z).comp
        ((underlyingBar k A).d (n + 1) n).hom := by
  let D : (A ⊗[k] TensorPower k (n + 2) A) →ₗ[k] (A ⊗[k] TensorPower k (n + 1) A) :=
    ((underlyingBar k A).d (n + 1) n).hom
  let F : Fin (n + 2) →
      (A ⊗[k] TensorPower k (n + 2) A) →ₗ[k] (A ⊗[k] TensorPower k (n + 1) A) :=
    fun i => (NonUnital.regularFace k A (n + 1) i.castSucc).hom
  have hd : D = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • F i := by
    have hs := ModuleCat.hom_sum (R := k)
      (M := NonUnital.chainLevel k A A (n + 2))
      (N := NonUnital.chainLevel k A A (n + 1))
      (fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val •
        NonUnital.regularFace k A (n + 1) i.castSucc) Finset.univ
    have hs' :
        ((∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          NonUnital.regularFace k A (n + 1) i.castSucc) :
          NonUnital.chainLevel k A A (n + 2) ⟶ NonUnital.chainLevel k A A (n + 1)).hom =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • F i := by
      simpa only [ModuleCat.hom_zsmul, F] using hs
    exact (congrArg (fun f : (underlyingBar k A).X (n + 1) ⟶
      (underlyingBar k A).X n => f.hom) (underlyingBar_d k A n)).trans hs'
  apply LinearMap.ext
  intro x
  change D (TensorPower.outerRepresentation k A (n + 1) z x) =
    TensorPower.outerRepresentation k A n z (D x)
  rw [hd]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun y => ((-1 : ℤ) ^ i.val) • y)
    (DFunLike.congr_fun (barAdjacentFace_intertwines k A n i z) x)

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
The bar differential is an E-linear map from
A ⊗[k] A^{⊗(n+2)} to A ⊗[k] A^{⊗(n+1)}, where E
acts on the two outer factors of each term. Its value is the alternating
sum ∑_{i=0}^{n+1} (−1)^i δ_i of adjacent multiplications. -/
def envelopingBoundaryLinear (n : ℕ) :
    letI := TensorPower.outerModule k A (n + 1)
    letI := TensorPower.outerModule k A n
    (A ⊗[k] TensorPower k (n + 2) A) →ₗ[EnvelopingAlgebra k A]
      (A ⊗[k] TensorPower k (n + 1) A) := by
  let := TensorPower.outerModule k A (n + 1)
  let := TensorPower.outerModule k A n
  exact {
    toFun := ((underlyingBar k A).d (n + 1) n).hom
    map_add' := ((underlyingBar k A).d (n + 1) n).hom.map_add
    map_smul' := fun z x => by
      change ((underlyingBar k A).d (n + 1) n).hom
        (TensorPower.outerRepresentation k A (n + 1) z x) =
          TensorPower.outerRepresentation k A n z
            (((underlyingBar k A).d (n + 1) n).hom x)
      exact DFunLike.congr_fun (underlyingBarBoundary_intertwines k A n z) x }

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
The degree-n left E-module of the bar complex is
A ⊗[k] A^{⊗(n+1)}, with (u ⊗ vᵐᵒᵖ) acting by left
multiplication by u on the first factor and right multiplication by v on
the last factor. It lies in ModuleCat at universe max{u,v}. -/
def envelopingBarDegree (n : ℕ) : ModuleCat.{max u v} (EnvelopingAlgebra k A) := by
  let := TensorPower.outerModule k A n
  exact ModuleCat.of (EnvelopingAlgebra k A) (A ⊗[k] TensorPower k (n + 1) A)

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
Between the left E-modules P_{n+1} and P_n, the bar differential
is the E-linear morphism whose value is
∑_{i=0}^{n+1} (−1)^i δ_i. -/
def envelopingBarBoundary (n : ℕ) : envelopingBarDegree k A (n + 1) ⟶ envelopingBarDegree k A n := by
  let : Module (EnvelopingAlgebra k A) (A ⊗[k] TensorPower k (n + 2) A) :=
    TensorPower.outerModule k A (n + 1)
  let : Module (EnvelopingAlgebra k A) (A ⊗[k] TensorPower k (n + 1) A) :=
    TensorPower.outerModule k A n
  exact ModuleCat.ofHom (envelopingBoundaryLinear k A n)

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
The adjacent-product bar differential satisfies
P_{n+2} → P_{n+1} → P_n = 0 as a composite of E-linear maps.
Thus two consecutive alternating adjacent-multiplication boundaries
have zero composite. -/
theorem envelopingBarBoundary_square (n : ℕ) :
    envelopingBarBoundary k A (n + 1) ≫ envelopingBarBoundary k A n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero]
  change ((underlyingBar k A).d (n + 1) n).hom
    (((underlyingBar k A).d (n + 2) (n + 1)).hom x) = 0
  have h := ConcreteCategory.congr_hom
    ((underlyingBar k A).d_comp_d (n + 2) (n + 1) n) x
  change ((underlyingBar k A).d (n + 1) n).hom
    (((underlyingBar k A).d (n + 2) (n + 1)).hom x) = 0 at h
  exact h

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
The terms P_n = A ⊗[k] A^{⊗(n+1)}, with their outer
E-actions and alternating adjacent-multiplication differentials, form
a chain complex of left E-modules indexed by ℕ. Its module universe is
max{u,v}. -/
def envelopingBar : ChainComplex (ModuleCat.{max u v} (EnvelopingAlgebra k A)) ℕ :=
  ChainComplex.of (envelopingBarDegree k A) (envelopingBarBoundary k A)
    (envelopingBarBoundary_square k A)

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
The differential of the E-module bar complex has the same value as
the k-linear adjacent-product bar differential on every
x ∈ P_{n+1}: d^E_{n+1}(x) = d^k_{n+1}(x). -/
theorem envelopingBar_d_apply (n : ℕ) (x : envelopingBarDegree k A (n + 1)) :
    ((envelopingBar k A).d (n + 1) n).hom x = ((underlyingBar k A).d (n + 1) n).hom x :=
  congrArg (fun f : envelopingBarDegree k A (n + 1) ⟶ envelopingBarDegree k A n => f.hom x)
    (ChainComplex.of_d (envelopingBarDegree k A) (envelopingBarBoundary k A) n)

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
The algebra A is a left E-module through the regular representation:
(a ⊗ bᵐᵒᵖ) • x = axb. -/
@[instance_reducible]
def regularEnvelopingModule : Module (EnvelopingAlgebra k A) A :=
  Module.compHom A (regularEnvelopingAction (k := k) (A := A)).toRingHom

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
Multiplication ε : P_0 = A ⊗[k] A → A is equivariant for
the outer action on P_0 and the regular action on A:
ε(z • x) = z • ε(x). On elementary tensors this is
ε((u ⊗ vᵐᵒᵖ) • (a ⊗ b)) = u(ab)v. -/
theorem underlyingBarAugmentation_intertwines (z : EnvelopingAlgebra k A) :
    (underlyingBarAugmentationLinear k A).comp (TensorPower.outerRepresentation k A 0 z) =
      (regularEnvelopingAction (k := k) (A := A) z).comp
        (underlyingBarAugmentationLinear k A) := by
  let f : (A ⊗[k] TensorPower k 1 A) →ₗ[k] A := underlyingBarAugmentationLinear k A
  have hf : ∀ (m : A) (a : Fin 1 → A), f (m ⊗ₜ[k] PiTensorProduct.tprod k a) = m * a 0 := by
    intro m a
    exact underlyingBarAugmentationLinear_tprod k A m a
  induction z using TensorProduct.inductionOn with
  | tmul l r =>
      apply tensorPower_ext
        (f := f.comp (TensorPower.outerRepresentation k A 0 (l ⊗ₜ[k] r)))
        (g := (regularEnvelopingAction (k := k) (A := A) (l ⊗ₜ[k] r)).comp f)
      intro a₀ a
      simp only [LinearMap.comp_apply]
      have hout := TensorPower.outerModule_tprod k A 0 l r.unop a₀ a
      change TensorPower.outerRepresentation k A 0 (l ⊗ₜ[k] MulOpposite.op r.unop)
        (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) = _ at hout
      rw [MulOpposite.op_unop] at hout
      rw [hout, hf, hf]
      have hc : (Fin.snoc (α := fun _ : Fin 1 => A) (Fin.init a)
          (a (Fin.last 0) * r.unop)) 0 = a 0 * r.unop := by
        have hlast := Fin.snoc_last (n := 0) (α := fun _ : Fin 1 => A)
          (x := a (Fin.last 0) * r.unop) (p := Fin.init a)
        change (Fin.snoc (α := fun _ : Fin 1 => A) (Fin.init a)
          (a (Fin.last 0) * r.unop)) 0 = a 0 * r.unop at hlast
        exact hlast
      simpa only [regularEnvelopingAction, AlgHom.mulLeftRight_apply, mul_assoc] using
        congrArg (fun c : A => l * (a₀ * c)) hc
  | add z w hz hw =>
      apply LinearMap.ext
      intro x
      change f (TensorPower.outerRepresentation k A 0 (z + w) x) =
        regularEnvelopingAction (k := k) (A := A) (z + w) (f x)
      rw [map_add, map_add]
      change f (TensorPower.outerRepresentation k A 0 z x +
        TensorPower.outerRepresentation k A 0 w x) =
          regularEnvelopingAction (k := k) (A := A) z (f x) +
            regularEnvelopingAction (k := k) (A := A) w (f x)
      exact (f.map_add _ _).trans
        (congrArg₂ (· + ·) (DFunLike.congr_fun hz x) (DFunLike.congr_fun hw x))

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
Multiplication ε(a ⊗ b) = ab defines an E-linear map
A ⊗[k] A → A, with the outer E-action on the domain and
the regular E-action on the codomain. -/
def envelopingAugmentationLinear :
    letI := TensorPower.outerModule k A 0
    letI := regularEnvelopingModule k A
    (A ⊗[k] TensorPower k 1 A) →ₗ[EnvelopingAlgebra k A] A := by
  let := TensorPower.outerModule k A 0
  let := regularEnvelopingModule k A
  exact {
    toFun := underlyingBarAugmentationLinear k A
    map_add' := (underlyingBarAugmentationLinear k A).map_add
    map_smul' := fun z x => by
      change underlyingBarAugmentationLinear k A (TensorPower.outerRepresentation k A 0 z x) =
        regularEnvelopingAction (k := k) (A := A) z (underlyingBarAugmentationLinear k A x)
      exact DFunLike.congr_fun (underlyingBarAugmentation_intertwines k A z) x }

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
The augmentation target is the regular left E-module A lifted to
universe max{u,v}, with (a ⊗ bᵐᵒᵖ) • ULift(x) = ULift(axb). -/
def regularEnvelopingTarget : ModuleCat.{max u v} (EnvelopingAlgebra k A) := by
  let := regularEnvelopingModule k A
  exact ModuleCat.of (EnvelopingAlgebra k A) (ULift.{max u v} A)

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
Multiplication defines the E-linear augmentation from bar degree zero
to the lifted regular module A. It sends a ⊗ b to ULift(ab). -/
def envelopingBarAugmentation : (envelopingBar k A).X 0 ⟶ regularEnvelopingTarget k A := by
  let : Module (EnvelopingAlgebra k A) (A ⊗[k] TensorPower k 1 A) :=
    TensorPower.outerModule k A 0
  let := regularEnvelopingModule k A
  exact ModuleCat.ofHom
    ((ULift.moduleEquiv.symm.toLinearMap : A →ₗ[EnvelopingAlgebra k A] ULift.{max u v} A).comp
      (envelopingAugmentationLinear k A))

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
For x in bar degree zero, the augmentation to the lifted regular
E-module A has value ULift(ε(x)), where ε : A ⊗[k] A → A
is multiplication. -/
theorem envelopingBarAugmentation_apply (x : (envelopingBar k A).X 0) :
    (envelopingBarAugmentation k A).hom x = ULift.up (underlyingBarAugmentationLinear k A x) := by
  simp only [envelopingBarAugmentation]
  rfl

/-- For a commutative ring k and an associative unital k-algebra A,
put E = A ⊗[k] Aᵐᵒᵖ.
The augmentation to the lifted regular E-module A satisfies
ε d_1 = 0. On a three-factor tensor, associativity gives
(ab)c − a(bc) = 0. -/
theorem envelopingBar_d_augmentation :
    (envelopingBar k A).d 1 0 ≫ envelopingBarAugmentation k A = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero]
  change (envelopingBarAugmentation k A).hom (((envelopingBar k A).d 1 0).hom x) = 0
  let F : (A ⊗[k] TensorPower k 1 A) →ₗ[k] A := underlyingBarAugmentationLinear k A
  have hD : (show A ⊗[k] TensorPower k 1 A from ((envelopingBar k A).d 1 0).hom x) =
      (show A ⊗[k] TensorPower k 1 A from ((underlyingBar k A).d 1 0).hom x) :=
    envelopingBar_d_apply k A 0 x
  have hc := congrArg (fun y : A ⊗[k] TensorPower k 1 A =>
    (ULift.up (F y) : ULift.{max u v} A)) hD
  have h := ConcreteCategory.congr_hom (underlyingBar_d_augmentation k A) x
  change ULift.up (F (((underlyingBar k A).d 1 0).hom x)) = 0 at h
  have ha := envelopingBarAugmentation_apply k A (((envelopingBar k A).d 1 0).hom x)
  change (envelopingBarAugmentation k A).hom (((envelopingBar k A).d 1 0).hom x) =
    (ULift.up (F (((envelopingBar k A).d 1 0).hom x)) : ULift.{max u v} A) at ha
  exact ha.trans (hc.trans h)

end ModuleCat.Algebra.Hochschild.AdjacentBar
