/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentPushout
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentHigherForms
public import MathlibExt.Algebra.Category.ModuleCat.ExteriorPower

/-!
# Tensor pushout of coefficient forms in every weight

Let `k : Type u` and `K : Type w` be commutative rings with `Algebra k K`, `A :
CommAlgCat.{max u v w} k`, and `B=K ⊗_k A`. For `P→A`, every coefficient-form weight has a
natural comparison after pushout to `P_K=K ⊗_k P` over `B`.

Weight zero is the regular tensor module `A ⊗_P P`. Its comparison uses the regular-module
tensor unitors. Positive weights are identified with exterior powers of cotangent
linearization; exterior-power base change and the cotangent pushout isomorphism give their
comparisons. On differential words the coefficient becomes `b·j_A(a)` and each argument `p_i`
becomes `j_P(p_i)`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Functor
open scoped TensorProduct

universe u v w

namespace CommAlgCat.CotangentPushout

variable (k : Type u) (K : Type w) [CommRing k] [CommRing K] [Algebra k K]
  (A : CommAlgCat.{max u v w} k)

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] tensorGroundAlgebra tensorRightAlgebra
attribute [local instance] overGroundAlgebra overRightAlgebra

/-- Let `K,A` be commutative `k`-algebras, `B=K ⊗_k A`, `P∈Over A`, and `P_K=K ⊗_k P.left`. The
isomorphism `zeroIso k K A P` identifies `B ⊗_A (A ⊗_{P.left} P.left)` with `B ⊗_{P_K} P_K`.
It composes the two regular-module unitors with the coefficient-extension unitor `B ⊗_A A ≅
B`. -/
def zeroIso (P : Over A) :
    (moduleFunctor.{u, v, w} k K A).obj (cotangentHigherLevel.{u, max v w} k A 0 P) ≅
      cotangentHigherLevel.{w, max u v} K (target.{u, v, w} k K A) 0 ((overFunctor.{u, v, w} k K A).obj P) :=
  (moduleFunctor.{u, v, w} k K A).mapIso (cotangentWeightZeroLevelIso.{u, max v w} k A P) ≪≫
    (TensorProduct.AlgebraTensorModule.rid A (target.{u, v, w} k K A) (target.{u, v, w} k K A)).toModuleIso ≪≫
        (cotangentWeightZeroLevelIso.{w, max u v} K (target.{u, v, w} k K A)
          ((overFunctor.{u, v, w} k K A).obj P)).symm

/-- Let `K,A` be commutative `k`-algebras, `B=K ⊗_k A`, and `f : P → Q` in `Over A`. For
coefficient extension `E`, pushed-out source functor `F`, and weight-zero form maps `F⁰`,
`E(F⁰(f)) ≫ zeroIso_Q.hom = zeroIso_P.hom ≫ F⁰_K(F.map f)`. These maps use the regular
coefficient modules `A ⊗_P P` and `B ⊗_{P_K} P_K`. -/
@[reassoc]
theorem zeroIso_naturality {P Q : Over A} (f : P ⟶ Q) :
    (moduleFunctor.{u, v, w} k K A).map (cotangentHigherMap.{u, max v w} k A 0 f) ≫
        (zeroIso.{u, v, w} k K A Q).hom =
      (zeroIso.{u, v, w} k K A P).hom ≫
        cotangentHigherMap.{w, max u v} K (target.{u, v, w} k K A) 0 ((overFunctor.{u, v, w} k K A).map f) := by
  let F : ModuleCat.{max u v w} A ⥤ ModuleCat.{max u v w} (target.{u, v, w} k K A) :=
    moduleFunctor.{u, v, w} k K A
  let rP := cotangentWeightZeroLevelIso.{u, max v w} k A P
  let rQ := cotangentWeightZeroLevelIso.{u, max v w} k A Q
  let sP := cotangentWeightZeroLevelIso.{w, max u v} K (target.{u, v, w} k K A)
    ((overFunctor.{u, v, w} k K A).obj P)
  let sQ := cotangentWeightZeroLevelIso.{w, max u v} K (target.{u, v, w} k K A)
    ((overFunctor.{u, v, w} k K A).obj Q)
  let e := (TensorProduct.AlgebraTensorModule.rid A
    (target.{u, v, w} k K A) (target.{u, v, w} k K A)).toModuleIso
  rw [cotangentHigherMap_zero_eq_weightZero.{u, max v w} k A f,
    cotangentHigherMap_zero_eq_weightZero.{w, max u v} K (target.{u, v, w} k K A)
      ((overFunctor.{u, v, w} k K A).map f)]
  change F.map (rP.hom ≫ rQ.inv) ≫ (F.map rQ.hom ≫ e.hom ≫ sQ.inv) =
    (F.map rP.hom ≫ e.hom ≫ sP.inv) ≫ (sP.hom ≫ sQ.inv)
  have hComp : F.map (rP.hom ≫ rQ.inv) = F.map rP.hom ≫ F.map rQ.inv := F.map_comp _ _
  have hCancel : F.map rQ.inv ≫ F.map rQ.hom = 𝟙 (F.obj (ModuleCat.of A A)) :=
    (F.map_comp rQ.inv rQ.hom).symm.trans
      ((congrArg F.map rQ.inv_hom_id).trans (F.map_id _))
  rw [hComp]
  calc
    (F.map rP.hom ≫ F.map rQ.inv) ≫ (F.map rQ.hom ≫ e.hom ≫ sQ.inv) =
        F.map rP.hom ≫ (F.map rQ.inv ≫ F.map rQ.hom) ≫ e.hom ≫ sQ.inv := by
      simp only [Category.assoc]
    _ = F.map rP.hom ≫ e.hom ≫ sQ.inv := by rw [hCancel, Category.id_comp]
    _ = F.map rP.hom ≫ e.hom ≫ (sP.inv ≫ sP.hom) ≫ sQ.inv := by
      rw [sP.inv_hom_id, Category.id_comp]
    _ = (F.map rP.hom ≫ e.hom ≫ sP.inv) ≫ (sP.hom ≫ sQ.inv) := by
      have h₁ := Category.assoc sP.inv sP.hom sQ.inv
      have h₂ := Category.assoc e.hom sP.inv (sP.hom ≫ sQ.inv)
      have h₃ := Category.assoc (F.map rP.hom) (e.hom ≫ sP.inv) (sP.hom ≫ sQ.inv)
      exact (congrArg (fun m => F.map rP.hom ≫ e.hom ≫ m) h₁).trans
        ((congrArg (fun m => F.map rP.hom ≫ m) h₂.symm).trans h₃.symm)

/-- For commutative `k`-algebras `K,A` and `B=K ⊗_k A`, the weight-zero coefficient-form functor
followed by extension `A→B` is naturally isomorphic to tensor pushout on `Over A` followed by
the weight-zero functor over `K,B`. Its component is `zeroIso k K A P`. -/
def zeroNatIso :
    cotangentHigherFunctor.{u, max v w} k A 0 ⋙ moduleFunctor.{u, v, w} k K A ≅
      overFunctor.{u, v, w} k K A ⋙ cotangentHigherFunctor.{w, max u v} K (target.{u, v, w} k K A) 0 :=
  NatIso.ofComponents (zeroIso.{u, v, w} k K A) (zeroIso_naturality.{u, v, w} k K A)

/-- Let `K,A` be commutative `k`-algebras, `P∈Over A`, `B=K ⊗_k A`, `b∈B`, `a∈A`, and `p∈P.left`.
The forward weight-zero comparison sends `b ⊗_A (a ⊗_{P.left} p)` to `b·j_A(a) ⊗_{P_K}
j_P(p)`, where `P_K=K ⊗_k P.left` and `j_A,j_P` are the right tensor inclusions. -/
@[simp]
theorem zeroIso_tmul (P : Over A) (b : target.{u, v, w} k K A) (a : A) (p : P.left) :
    letI : Algebra P.left A := CommAlgCat.cotangentAlgebra.{u, max v w} k A P
    letI : Algebra ((overFunctor.{u, v, w} k K A).obj P).left (target.{u, v, w} k K A) :=
      CommAlgCat.cotangentAlgebra.{w, max u v} K (target.{u, v, w} k K A)
        ((overFunctor.{u, v, w} k K A).obj P)
    letI : Algebra ((overFunctor.{u, v, w} k K A).obj P).left
        ((algebraFunctor.{u, v, w} k K).obj P.left) :=
      Algebra.id ((overFunctor.{u, v, w} k K A).obj P).left
    (zeroIso.{u, v, w} k K A P).hom.hom (b ⊗ₜ[A] (a ⊗ₜ[P.left] p)) =
      (b * algebraMap A (target.{u, v, w} k K A) a) ⊗ₜ[((overFunctor.{u, v, w} k K A).obj P).left]
        algebraUnit.{u, v, w} k K P.left p := by
  let B := target.{u, v, w} k K A
  let Q := (overFunctor.{u, v, w} k K A).obj P
  letI : Algebra P.left A := CommAlgCat.cotangentAlgebra.{u, max v w} k A P
  letI : Algebra Q.left B := CommAlgCat.cotangentAlgebra.{w, max u v} K B Q
  let F : ModuleCat.{max u v w} A ⥤ ModuleCat.{max u v w} B := moduleFunctor.{u, v, w} k K A
  let rP : cotangentHigherLevel.{u, max v w} k A 0 P ≅ ModuleCat.of A A :=
    cotangentWeightZeroLevelIso.{u, max v w} k A P
  let rQ : cotangentHigherLevel.{w, max u v} K B 0 Q ≅ ModuleCat.of B B :=
    cotangentWeightZeroLevelIso.{w, max u v} K B Q
  let e : F.obj (ModuleCat.of A A) ≅ ModuleCat.of B B :=
    (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso
  let l : F.obj (cotangentHigherLevel.{u, max v w} k A 0 P) ⟶ F.obj (ModuleCat.of A A) :=
    F.map rP.hom
  let x : F.obj (cotangentHigherLevel.{u, max v w} k A 0 P) := b ⊗ₜ[A] (a ⊗ₜ[P.left] p)
  let y : cotangentHigherLevel.{w, max u v} K B 0 Q :=
    (b * algebraMap A B a) ⊗ₜ[Q.left] algebraUnit.{u, v, w} k K P.left p
  have hComponent : (zeroIso.{u, v, w} k K A P).hom = l ≫ e.hom ≫ rQ.inv := rfl
  have hP : rP.hom (a ⊗ₜ[P.left] p) = P.hom.hom p * a :=
    cotangentWeightZeroLevelIso_tmul.{u, max v w} k A P a p
  have hMap : l x = b ⊗ₜ[A] (P.hom.hom p * a) :=
    (ModuleCat.ExtendScalars.map_tmul (algebraMap A B) rP.hom b (a ⊗ₜ[P.left] p)).trans
      (congrArg (fun z : ModuleCat.of A A => b ⊗ₜ[A] z) hP)
  have hRid : e.hom (b ⊗ₜ[A] (P.hom.hom p * a)) = algebraMap A B (P.hom.hom p * a) * b :=
    (TensorProduct.AlgebraTensorModule.rid_tmul B (P.hom.hom p * a) b).trans
      (Algebra.smul_def _ _)
  have hQ : rQ.hom y = Q.hom.hom (algebraUnit.{u, v, w} k K P.left p) * (b * algebraMap A B a) :=
    cotangentWeightZeroLevelIso_tmul.{w, max u v} K B Q
      (b * algebraMap A B a) (algebraUnit.{u, v, w} k K P.left p)
  have hAug : Q.hom.hom (algebraUnit.{u, v, w} k K P.left p) = algebraMap A B (P.hom.hom p) :=
    algebraUnit_augmentation.{u, v, w} k K A P p
  have hProducts : algebraMap A B (P.hom.hom p * a) * b =
      Q.hom.hom (algebraUnit.{u, v, w} k K P.left p) * (b * algebraMap A B a) := by
    rw [hAug, map_mul]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  have hApply : (zeroIso.{u, v, w} k K A P).hom x = rQ.inv (e.hom (l x)) :=
    (congrArg (fun m => m x) hComponent).trans rfl
  apply (ModuleCat.mono_iff_injective rQ.hom).mp inferInstance
  exact (congrArg rQ.hom.hom hApply).trans
    ((ModuleCat.hom_inv_apply rQ (e.hom (l x))).trans
      ((congrArg e.hom.hom hMap).trans (hRid.trans (hProducts.trans hQ.symm))))

/-- Let `K,A` be commutative `k`-algebras, `P∈Over A`, and `B=K ⊗_k A`. For `b∈B` and `p∈P.left`,
the inverse weight-zero comparison sends `b ⊗_{P_K} j_P(p)` to `b ⊗_A (1 ⊗_{P.left} p)`, using
the induced source actions through the augmentations. -/
@[simp]
theorem zeroIso_inv_tmul (P : Over A) (b : target.{u, v, w} k K A) (p : P.left) :
    letI : Algebra P.left A := CommAlgCat.cotangentAlgebra.{u, max v w} k A P
    letI : Algebra ((overFunctor.{u, v, w} k K A).obj P).left (target.{u, v, w} k K A) :=
      CommAlgCat.cotangentAlgebra.{w, max u v} K (target.{u, v, w} k K A) ((overFunctor.{u, v, w} k K A).obj P)
    letI : Algebra ((overFunctor.{u, v, w} k K A).obj P).left
        ((algebraFunctor.{u, v, w} k K).obj P.left) :=
      Algebra.id ((overFunctor.{u, v, w} k K A).obj P).left
    (zeroIso.{u, v, w} k K A P).inv.hom
        (b ⊗ₜ[((overFunctor.{u, v, w} k K A).obj P).left] algebraUnit.{u, v, w} k K P.left p) =
      b ⊗ₜ[A] ((1 : A) ⊗ₜ[P.left] p) := by
  letI : Algebra P.left A := CommAlgCat.cotangentAlgebra.{u, max v w} k A P
  letI : Algebra ((overFunctor.{u, v, w} k K A).obj P).left (target.{u, v, w} k K A) :=
    CommAlgCat.cotangentAlgebra.{w, max u v} K (target.{u, v, w} k K A) ((overFunctor.{u, v, w} k K A).obj P)
  letI : Algebra ((overFunctor.{u, v, w} k K A).obj P).left
      ((algebraFunctor.{u, v, w} k K).obj P.left) :=
    Algebra.id ((overFunctor.{u, v, w} k K A).obj P).left
  let e := zeroIso.{u, v, w} k K A P
  let x : (moduleFunctor.{u, v, w} k K A).obj (cotangentHigherLevel.{u, max v w} k A 0 P) :=
    b ⊗ₜ[A] ((1 : A) ⊗ₜ[P.left] p)
  have hx : e.hom x =
      b ⊗ₜ[((overFunctor.{u, v, w} k K A).obj P).left] algebraUnit.{u, v, w} k K P.left p := by
    have h := zeroIso_tmul.{u, v, w} k K A P b 1 p
    simpa only [map_one, mul_one] using h
  exact (congrArg e.inv.hom hx).symm.trans (ModuleCat.inv_hom_apply e x)

/-- Let `K,A` be commutative `k`-algebras, `B=K ⊗_k A`, and `n : ℕ`. The weight-`n+1`
coefficient-form functor followed by coefficient extension `A→B` is naturally isomorphic to
source tensor pushout followed by the weight-`n+1` functor over `K,B`. The comparison
identifies positive forms with exterior powers, applies exterior-power base change and the
cotangent pushout isomorphism, then returns to the higher-form model. -/
def positiveNatIso (n : ℕ) :
    cotangentHigherFunctor.{u, max v w} k A (n + 1) ⋙ moduleFunctor.{u, v, w} k K A ≅
      overFunctor.{u, v, w} k K A ⋙
        cotangentHigherFunctor.{w, max u v} K (target.{u, v, w} k K A) (n + 1) :=
  isoWhiskerRight (cotangentHigherExteriorNatIso.{u, max v w} k A (n + 1))
      (moduleFunctor.{u, v, w} k K A) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (CommAlgCat.cotangentFunctor.{u, max v w} k A)
      (ModuleCat.exteriorPowerBaseChangeNatIso.{max u v w, 0, max u v w}
        A (target.{u, v, w} k K A) (n + 1)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (cotangentNatIso.{u, v, w} k K A)
      (ModuleCat.exteriorPowerFunctorAt.{max u v w, max u v w} (target.{u, v, w} k K A) (n + 1)) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (overFunctor.{u, v, w} k K A)
      (cotangentHigherExteriorNatIso.{w, max u v} K (target.{u, v, w} k K A) (n + 1)).symm

/-- Let `K,A` be commutative `k`-algebras and `B=K ⊗_k A`. For every `p : ℕ`, the coefficient-form
functor of weight `p` over `k,A`, followed by extension `A→B`, is naturally isomorphic to
source tensor pushout followed by the weight-`p` functor over `K,B`. Weight zero uses the
regular tensor unitors; positive weights use exterior-power base change and the cotangent
comparison. -/
def higherNatIso (n : ℕ) :
    cotangentHigherFunctor.{u, max v w} k A n ⋙ moduleFunctor.{u, v, w} k K A ≅
      overFunctor.{u, v, w} k K A ⋙ cotangentHigherFunctor.{w, max u v} K (target.{u, v, w} k K A) n :=
  match n with
  | 0 => zeroNatIso.{u, v, w} k K A
  | n + 1 => positiveNatIso.{u, v, w} k K A n

/-- For commutative `k`-algebras `K,A`, `B=K ⊗_k A`, `P∈Over A`, and `p : ℕ`, `higherIso k K A p
P` identifies `B ⊗_A cotangentHigherLevel k A p P` with `cotangentHigherLevel K B p (P_K→B)`,
where `P_K=K ⊗_k P.left`. It is the component of the all-weight natural comparison. -/
def higherIso (n : ℕ) (P : Over A) :
    (moduleFunctor.{u, v, w} k K A).obj (cotangentHigherLevel.{u, max v w} k A n P) ≅
      cotangentHigherLevel.{w, max u v} K (target.{u, v, w} k K A) n ((overFunctor.{u, v, w} k K A).obj P) :=
  (higherNatIso.{u, v, w} k K A n).app P

/-- Let `K,A` be commutative `k`-algebras, `B=K ⊗_k A`, `P∈Over A`, and `p=n+1`. Write `φ_A,φ_B`
for the positive-form/exterior-power identifications, `β` for exterior-power base change `B
⊗_A ∧_A^p C ≅ ∧_B^p(B ⊗_A C)`, and `γ_P` for cotangent pushout. The forward weight-`p`
comparison is `E(φ_A.hom) ≫ β.hom ≫ (∧_B^p γ_P.hom) ≫ φ_B.inv`, where `E=B ⊗_A -` and
`C=cotangent k A P`. -/
theorem higherIso_hom_succ (n : ℕ) (P : Over A) :
    (higherIso.{u, v, w} k K A (n + 1) P).hom =
      (moduleFunctor.{u, v, w} k K A).map (cotangentHigherExteriorIso.{u, max v w} k A (n + 1) P).hom ≫
        ((ModuleCat.exteriorPowerBaseChangeNatIso.{max u v w, 0, max u v w}
          A (target.{u, v, w} k K A) (n + 1)).hom.app (CommAlgCat.cotangent.{u, max v w} k A P)) ≫
        (ModuleCat.exteriorPowerFunctorAt.{max u v w, max u v w} (target.{u, v, w} k K A) (n + 1)).map
          (cotangentIso.{u, v, w} k K A P).hom ≫
        (cotangentHigherExteriorIso.{w, max u v} K (target.{u, v, w} k K A) (n + 1)
          ((overFunctor.{u, v, w} k K A).obj P)).inv := by
  let B := target.{u, v, w} k K A
  let Q := (overFunctor.{u, v, w} k K A).obj P
  let F : ModuleCat.{max u v w} A ⥤ ModuleCat.{max u v w} B := moduleFunctor.{u, v, w} k K A
  let C := CommAlgCat.cotangent.{u, max v w} k A P
  let T := CommAlgCat.cotangent.{w, max u v} K B Q
  let EP := ModuleCat.exteriorPowerFunctorAt.{max u v w, max u v w} A (n + 1)
  let EQ := ModuleCat.exteriorPowerFunctorAt.{max u v w, max u v w} B (n + 1)
  let eP : cotangentHigherLevel.{u, max v w} k A (n + 1) P ≅ EP.obj C :=
    cotangentHigherExteriorIso.{u, max v w} k A (n + 1) P
  let eQ : cotangentHigherLevel.{w, max u v} K B (n + 1) Q ≅ EQ.obj T :=
    cotangentHigherExteriorIso.{w, max u v} K B (n + 1) Q
  have hP : (cotangentHigherExteriorNatIso.{u, max v w} k A (n + 1)).hom.app P = eP.hom := rfl
  have hQ : (cotangentHigherExteriorNatIso.{w, max u v} K B (n + 1)).inv.app Q = eQ.inv := rfl
  have hCot : (cotangentNatIso.{u, v, w} k K A).hom.app P = (cotangentIso.{u, v, w} k K A P).hom := rfl
  have hObj : (CommAlgCat.cotangentFunctor.{u, max v w} k A).obj P = C := rfl
  let α := isoWhiskerRight (cotangentHigherExteriorNatIso.{u, max v w} k A (n + 1)) F
  let β := Functor.associator (CommAlgCat.cotangentFunctor.{u, max v w} k A) EP F
  let γ := isoWhiskerLeft (CommAlgCat.cotangentFunctor.{u, max v w} k A)
    (ModuleCat.exteriorPowerBaseChangeNatIso.{max u v w, 0, max u v w} A B (n + 1))
  let δ := (Functor.associator (CommAlgCat.cotangentFunctor.{u, max v w} k A) F EQ).symm
  let ε := isoWhiskerRight (cotangentNatIso.{u, v, w} k K A) EQ
  let ζ := Functor.associator (overFunctor.{u, v, w} k K A)
    (CommAlgCat.cotangentFunctor.{w, max u v} K B) EQ
  let η := isoWhiskerLeft (overFunctor.{u, v, w} k K A)
    (cotangentHigherExteriorNatIso.{w, max u v} K B (n + 1)).symm
  let e := α ≪≫ β ≪≫ γ ≪≫ δ ≪≫ ε ≪≫ ζ ≪≫ η
  have hChain : (higherIso.{u, v, w} k K A (n + 1) P).hom = e.hom.app P := rfl
  have hα : α.hom.app P = F.map eP.hom := rfl
  have hβ : β.hom.app P = 𝟙 (F.obj (EP.obj C)) := rfl
  have hγ : γ.hom.app P =
      (ModuleCat.exteriorPowerBaseChangeNatIso.{max u v w, 0, max u v w} A B (n + 1)).hom.app C := rfl
  have hδ : δ.hom.app P = 𝟙 (EQ.obj (F.obj C)) := rfl
  have hε : ε.hom.app P = EQ.map (cotangentIso.{u, v, w} k K A P).hom := rfl
  have hζ : ζ.hom.app P = 𝟙 (EQ.obj T) := rfl
  have hη : η.hom.app P = eQ.inv := rfl
  have hComponents : e.hom.app P = α.hom.app P ≫ β.hom.app P ≫ γ.hom.app P ≫
      δ.hom.app P ≫ ε.hom.app P ≫ ζ.hom.app P ≫ η.hom.app P := rfl
  let U₀ : ModuleCat.{max u v w} B := F.obj (cotangentHigherLevel.{u, max v w} k A (n + 1) P)
  let U₁ : ModuleCat.{max u v w} B := F.obj (EP.obj C)
  let U₂ : ModuleCat.{max u v w} B := EQ.obj (F.obj C)
  let U₃ : ModuleCat.{max u v w} B := EQ.obj T
  let U₄ : ModuleCat.{max u v w} B := cotangentHigherLevel.{w, max u v} K B (n + 1) Q
  let l₀ : U₀ ⟶ U₁ := F.map eP.hom
  let l₁ : U₁ ⟶ U₂ :=
    (ModuleCat.exteriorPowerBaseChangeNatIso.{max u v w, 0, max u v w} A B (n + 1)).hom.app C
  let l₂ : U₂ ⟶ U₃ := EQ.map (cotangentIso.{u, v, w} k K A P).hom
  let l₃ : U₃ ⟶ U₄ := eQ.inv
  have hValue (x : U₀) : e.hom.app P x = l₃ (l₂ (l₁ (l₀ x))) := by
    have hApply : e.hom.app P x = η.hom.app P (ζ.hom.app P
        (ε.hom.app P (δ.hom.app P (γ.hom.app P (β.hom.app P (α.hom.app P x)))))) := rfl
    have ha : α.hom.app P x = l₀ x := congrArg (fun m => m x) hα
    have hb (z : U₁) : β.hom.app P z = z :=
      (congrArg (fun m => m z) hβ).trans (ModuleCat.id_apply U₁ z)
    have hc (z : U₁) : γ.hom.app P z = l₁ z := congrArg (fun m => m z) hγ
    have hd (z : U₂) : δ.hom.app P z = z :=
      (congrArg (fun m => m z) hδ).trans (ModuleCat.id_apply U₂ z)
    have he (z : U₂) : ε.hom.app P z = l₂ z := congrArg (fun m => m z) hε
    have hf (z : U₃) : ζ.hom.app P z = z :=
      (congrArg (fun m => m z) hζ).trans (ModuleCat.id_apply U₃ z)
    have hg (z : U₃) : η.hom.app P z = l₃ z := congrArg (fun m => m z) hη
    have h₀ : β.hom.app P (α.hom.app P x) = l₀ x :=
      (hb _).trans ha
    have h₁ : γ.hom.app P (β.hom.app P (α.hom.app P x)) = l₁ (l₀ x) :=
      (hc _).trans (congrArg l₁ h₀)
    have h₂ : δ.hom.app P (γ.hom.app P (β.hom.app P (α.hom.app P x))) = l₁ (l₀ x) :=
      (hd _).trans h₁
    have h₃ : ε.hom.app P (δ.hom.app P (γ.hom.app P (β.hom.app P (α.hom.app P x)))) =
        l₂ (l₁ (l₀ x)) :=
      (he _).trans (congrArg l₂ h₂)
    have h₄ : ζ.hom.app P (ε.hom.app P (δ.hom.app P (γ.hom.app P
        (β.hom.app P (α.hom.app P x))))) = l₂ (l₁ (l₀ x)) :=
      (hf _).trans h₃
    exact hApply.trans ((hg _).trans (congrArg l₃ h₄))

  have hMaps : e.hom.app P = l₀ ≫ l₁ ≫ l₂ ≫ l₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact hValue x
  exact hChain.trans hMaps


/-- Let `K,A` be commutative `k`-algebras, `B=K ⊗_k A`, `P∈Over A`, `n : ℕ`, `b∈B`, `a∈A`, and `p
: Fin(n+1) → P.left`. The forward weight-`n+1` map sends `b ⊗ (a ⊗ dp₀∧⋯∧dp_n)` to `b·j_A(a) ⊗
d(j_P p₀)∧⋯∧d(j_P p_n)`, where `j_A,j_P` are the right tensor inclusions. The displayed order
of differential factors is preserved. -/
@[simp]
theorem higherIso_tensor (n : ℕ) (P : Over A)
    (b : target.{u, v, w} k K A) (a : A) (p : Fin (n + 1) → P.left) :
    (higherIso.{u, v, w} k K A (n + 1) P).hom.hom
        (b ⊗ₜ[A] cotangentHigherTensor.{u, max v w} k A n P a p) =
      cotangentHigherTensor.{w, max u v} K (target.{u, v, w} k K A) n ((overFunctor.{u, v, w} k K A).obj P)
        (b * algebraMap A (target.{u, v, w} k K A) a)
        (fun i => algebraUnit.{u, v, w} k K P.left (p i)) := by
  let B := target.{u, v, w} k K A
  let Q := (overFunctor.{u, v, w} k K A).obj P
  let F : ModuleCat.{max u v w} A ⥤ ModuleCat.{max u v w} B := moduleFunctor.{u, v, w} k K A
  let EP := ModuleCat.exteriorPowerFunctorAt.{max u v w, max u v w} A (n + 1)
  let EQ := ModuleCat.exteriorPowerFunctorAt.{max u v w, max u v w} B (n + 1)
  let C := CommAlgCat.cotangent.{u, max v w} k A P
  let T := CommAlgCat.cotangent.{w, max u v} K B Q
  let eP : cotangentHigherLevel.{u, max v w} k A (n + 1) P ≅ EP.obj C :=
    cotangentHigherExteriorIso.{u, max v w} k A (n + 1) P
  let eQ : cotangentHigherLevel.{w, max u v} K B (n + 1) Q ≅ EQ.obj T :=
    cotangentHigherExteriorIso.{w, max u v} K B (n + 1) Q
  let eBase : F.obj (EP.obj C) ≅ EQ.obj (F.obj C) :=
    (ModuleCat.exteriorPowerBaseChangeNatIso.{max u v w, 0, max u v w} A B (n + 1)).app C
  let eCot : F.obj C ≅ T := cotangentIso.{u, v, w} k K A P
  let l₀ : F.obj (cotangentHigherLevel.{u, max v w} k A (n + 1) P) ⟶ F.obj (EP.obj C) :=
    F.map eP.hom
  let l₁ : EQ.obj (F.obj C) ⟶ EQ.obj T := EQ.map eCot.hom
  let x : F.obj (cotangentHigherLevel.{u, max v w} k A (n + 1) P) :=
    b ⊗ₜ[A] cotangentHigherTensor.{u, max v w} k A n P a p
  let y : cotangentHigherLevel.{w, max u v} K B (n + 1) Q :=
    cotangentHigherTensor.{w, max u v} K B n Q (b * algebraMap A B a)
      (fun i => algebraUnit.{u, v, w} k K P.left (p i))
  let vP : Fin (n + 1) → C := fun i => CommAlgCat.cotangentTensor.{u, max v w} k A P 1 (p i)
  let vB : Fin (n + 1) → F.obj C := fun i => (1 : B) ⊗ₜ[A] vP i
  let vQ : Fin (n + 1) → T :=
    fun i => CommAlgCat.cotangentTensor.{w, max u v} K B Q 1 (algebraUnit.{u, v, w} k K P.left (p i))
  have hP : eP.hom (cotangentHigherTensor.{u, max v w} k A n P a p) =
      a • exteriorPower.ιMulti A (n + 1) vP :=
    cotangentHigherExteriorIso_tensor.{u, max v w} k A n P a p
  have h₀ : l₀ x = (b * algebraMap A B a) ⊗ₜ[A] exteriorPower.ιMulti A (n + 1) vP := by
    have hMap := ModuleCat.ExtendScalars.map_tmul (algebraMap A B) eP.hom b
      (cotangentHigherTensor.{u, max v w} k A n P a p)
    refine hMap.trans ((congrArg (fun z : EP.obj C => b ⊗ₜ[A] z) hP).trans ?_)
    have hBalance : b ⊗ₜ[A] (a • exteriorPower.ιMulti A (n + 1) vP) =
        (a • b) ⊗ₜ[A] exteriorPower.ιMulti A (n + 1) vP :=
      (TensorProduct.tmul_smul a b _).trans (TensorProduct.smul_tmul' a b _)
    exact hBalance.trans (congrArg (fun z : B => z ⊗ₜ[A] exteriorPower.ιMulti A (n + 1) vP)
      ((Algebra.smul_def a b).trans (mul_comm _ _)))
  have hBase : eBase.hom ((b * algebraMap A B a) ⊗ₜ[A] exteriorPower.ιMulti A (n + 1) vP) =
      (b * algebraMap A B a) • exteriorPower.ιMulti B (n + 1) vB :=
    ModuleCat.exteriorPowerBaseChangeNatIso_hom_tmul_ιMulti.{max u v w, 0, max u v w}
      A B (n + 1) C (b * algebraMap A B a) vP
  have hCot (i : Fin (n + 1)) : eCot.hom (vB i) = vQ i := by
    have h := cotangentIso_tensor.{u, v, w} k K A P 1 1 (p i)
    simpa only [map_one, mul_one] using h
  let d : (⋀[B]^(n + 1) (F.obj C)) →ₗ[B] (⋀[B]^(n + 1) T) :=
    exteriorPower.map (n + 1) eCot.hom.hom
  have hValue (z : ⋀[B]^(n + 1) (F.obj C)) : l₁ z = d z := rfl
  have hWord : d (exteriorPower.ιMulti B (n + 1) vB) = exteriorPower.ιMulti B (n + 1) vQ :=
    (exteriorPower.map_apply_ιMulti eCot.hom.hom vB).trans
      (congrArg (exteriorPower.ιMulti B (n + 1)) (funext hCot))
  have h₁ : l₁ ((b * algebraMap A B a) • exteriorPower.ιMulti B (n + 1) vB) =
      (b * algebraMap A B a) • exteriorPower.ιMulti B (n + 1) vQ :=
    (hValue _).trans ((d.map_smul _ _).trans (congrArg (fun z => (b * algebraMap A B a) • z) hWord))
  have hQ : eQ.hom y = (b * algebraMap A B a) • exteriorPower.ιMulti B (n + 1) vQ :=
    cotangentHigherExteriorIso_tensor.{w, max u v} K B n Q (b * algebraMap A B a)
      (fun i => algebraUnit.{u, v, w} k K P.left (p i))
  have hComponent : (higherIso.{u, v, w} k K A (n + 1) P).hom =
      l₀ ≫ eBase.hom ≫ l₁ ≫ eQ.inv := higherIso_hom_succ.{u, v, w} k K A n P
  have hApply : (higherIso.{u, v, w} k K A (n + 1) P).hom x =
      eQ.inv (l₁ (eBase.hom (l₀ x))) :=
    (congrArg (fun m => m x) hComponent).trans rfl
  apply (ModuleCat.mono_iff_injective eQ.hom).mp inferInstance
  exact (congrArg eQ.hom.hom hApply).trans
    ((ModuleCat.hom_inv_apply eQ (l₁ (eBase.hom (l₀ x)))).trans
      ((congrArg (fun z => l₁ (eBase.hom z)) h₀).trans
        ((congrArg l₁.hom hBase).trans (h₁.trans hQ.symm))))

/-- Let `K,A` be commutative `k`-algebras, `B=K ⊗_k A`, `P∈Over A`, `n : ℕ`, and `p : Fin(n+1) →
P.left`. For `b∈B`, the inverse weight-`n+1` comparison sends the word with coefficient `b`
and factors `d(j_P p_i)` to `b ⊗_A cotangentHigherTensor k A n P 1 p`. Thus the source word
has coefficient one inside the outer coefficient tensor. -/
@[simp]
theorem higherIso_inv_tensor (n : ℕ) (P : Over A)
    (b : target.{u, v, w} k K A) (p : Fin (n + 1) → P.left) :
    (higherIso.{u, v, w} k K A (n + 1) P).inv.hom
        (cotangentHigherTensor.{w, max u v} K (target.{u, v, w} k K A) n ((overFunctor.{u, v, w} k K A).obj P)
          b (fun i => algebraUnit.{u, v, w} k K P.left (p i))) =
      b ⊗ₜ[A] cotangentHigherTensor.{u, max v w} k A n P 1 p := by
  let e := higherIso.{u, v, w} k K A (n + 1) P
  let x : (moduleFunctor.{u, v, w} k K A).obj
      (cotangentHigherLevel.{u, max v w} k A (n + 1) P) :=
    b ⊗ₜ[A] cotangentHigherTensor.{u, max v w} k A n P 1 p
  have hx : e.hom x =
      cotangentHigherTensor.{w, max u v} K (target.{u, v, w} k K A) n
        ((overFunctor.{u, v, w} k K A).obj P) b
          (fun i => algebraUnit.{u, v, w} k K P.left (p i)) := by
    have h := higherIso_tensor.{u, v, w} k K A n P b 1 p
    simpa only [map_one, mul_one] using h
  exact (congrArg e.inv.hom hx).symm.trans (ModuleCat.inv_hom_apply e x)

/-- Let `K,A` be commutative `k`-algebras, `B=K ⊗_k A`, `p : ℕ`, and `f : P → Q` in `Over A`. For
coefficient extension `E`, pushed-out algebra functor `F`, and form comparisons `η`,
`E(cotangentHigherMap k A p f) ≫ η_Q.hom = η_P.hom ≫ cotangentHigherMap K B p (F.map f)`. This
holds in weight zero and every positive weight. -/
@[reassoc]
theorem higherIso_naturality (n : ℕ) {P Q : Over A} (f : P ⟶ Q) :
    (moduleFunctor.{u, v, w} k K A).map (cotangentHigherMap.{u, max v w} k A n f) ≫
        (higherIso.{u, v, w} k K A n Q).hom =
      (higherIso.{u, v, w} k K A n P).hom ≫
        cotangentHigherMap.{w, max u v} K (target.{u, v, w} k K A) n ((overFunctor.{u, v, w} k K A).map f) :=
  (higherNatIso.{u, v, w} k K A n).hom.naturality f

end CommAlgCat.CotangentPushout

end
