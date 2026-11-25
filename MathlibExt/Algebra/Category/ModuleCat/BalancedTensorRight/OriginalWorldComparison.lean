/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.UniverseLongExact
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.TransportComparison

/-!
# Tor comparisons from the original source category

The original right-module category is assumed to have projective resolutions,
and its actual native universe lift is assumed to preserve projective objects.
These are the capabilities used by source precomposition. Ring smallness in the
original carrier universe is not required here. The established sufficient-world
comparisons retain their smallness hypotheses and are not changed by this module.

The comparison is the composition of exact target postcomposition, derivation of
the actual whole-output tensor isomorphism, and native source precomposition.
Its augmentation, connecting morphism and coefficient squares use those same
three comparisons. The outer ring needs no smallness or projective resolutions;
the coefficient module need not be projective.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe zGlobal rGlobal sGlobal vGlobal

namespace ModuleCat.BalancedTensorRight

variable (R : Type rGlobal) (S : Type sGlobal) [Ring R] [Ring S]
  (B : Type vGlobal) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
  [SMulCommClass R Sᵐᵒᵖ B]

section TensorCoefficients

variable (B' : Type vGlobal) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
  [SMulCommClass R Sᵐᵒᵖ B']
  (f : B →ₗ[R] B') (hf : ∀ (sGlobal : Sᵐᵒᵖ) (x : B), f (sGlobal • x) = sGlobal • f x)

/-- The whole-output tensor comparison respects the actual original coefficient map. -/
theorem tensorOriginalLiftIsoAt_natural_coefficient.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type v) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type v) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B'] (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) :
    tensorCoefficientTransformationAt.{z, r, s, v, v} R S B B' f hf ≫
        (tensorOriginalLiftIsoAt.{z, r, s, v} R S B').hom =
      (tensorOriginalLiftIsoAt.{z, r, s, v} R S B).hom ≫
        Functor.whiskerRight (tensorCoefficientTransformation R S B B' f hf)
          (ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ) := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R
    (ULift.{max r v z} X) (ULift.{max r v z} B)
  intro x y
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  change (tensorOutputLiftIsoAt R S B' X).hom.hom
      (((tensorCoefficientTransformationAt R S B B' f hf).app X).hom
        (TensorProduct.Balanced.mk ℤ R (ULift.{max r v z} X)
          (ULift.{max r v z} B) (ULift.up x) (ULift.up y))) =
    ((ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ).map
      ((tensorCoefficientTransformation R S B B' f hf).app X)).hom
        ((tensorOutputLiftIsoAt R S B X).hom.hom
          (TensorProduct.Balanced.mk ℤ R (ULift.{max r v z} X)
            (ULift.{max r v z} B) (ULift.up x) (ULift.up y)))
  rw [tensorCoefficientTransformationAt_mk, tensorOutputLiftIsoAt_hom_mk,
    tensorOutputLiftIsoAt_hom_mk]
  change ULift.up (TensorProduct.Balanced.mk ℤ R X B' x (f y)) =
    ULift.up ((tensorCoefficientMap R S B B' f hf X).hom
      (TensorProduct.Balanced.mk ℤ R X B x y))
  rw [tensorCoefficientMap_mk]
  rfl

end TensorCoefficients

section OriginalWindows

variable [HasProjectiveResolutions (ModuleCat.{vGlobal} Rᵐᵒᵖ)]

/-- Native derived input maps give the map between the original exact windows. -/
def originalTorLongSequenceMap (n : ℕ)
    (Q Q' : ShortComplex (ModuleCat.{vGlobal} Rᵐᵒᵖ)) (φ : Q ⟶ Q')
    (hQ : Q.ShortExact) (hQ' : Q'.ShortExact) :
    LeftDerivedDelta.LDlongSequence (tensorFunctor R S B) n Q hQ ⟶
      LeftDerivedDelta.LDlongSequence (tensorFunctor R S B) n Q' hQ' := by
  let F := tensorFunctor R S B
  refine ComposableArrows.homMk₅
    ((F.leftDerived (n + 1)).map φ.τ₁)
    ((F.leftDerived (n + 1)).map φ.τ₂)
    ((F.leftDerived (n + 1)).map φ.τ₃)
    ((F.leftDerived n).map φ.τ₁)
    ((F.leftDerived n).map φ.τ₂)
    ((F.leftDerived n).map φ.τ₃) ?_ ?_ ?_ ?_ ?_
  · change (F.leftDerived (n + 1)).map Q.f ≫
        (F.leftDerived (n + 1)).map φ.τ₂ =
      (F.leftDerived (n + 1)).map φ.τ₁ ≫ (F.leftDerived (n + 1)).map Q'.f
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁₂]
  · change (F.leftDerived (n + 1)).map Q.g ≫
        (F.leftDerived (n + 1)).map φ.τ₃ =
      (F.leftDerived (n + 1)).map φ.τ₂ ≫ (F.leftDerived (n + 1)).map Q'.g
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂₃]
  · exact (LeftDerivedDelta.LDdelta_natural F n Q' Q φ hQ' hQ).symm
  · change (F.leftDerived n).map Q.f ≫ (F.leftDerived n).map φ.τ₂ =
      (F.leftDerived n).map φ.τ₁ ≫ (F.leftDerived n).map Q'.f
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁₂]
  · change (F.leftDerived n).map Q.g ≫ (F.leftDerived n).map φ.τ₃ =
      (F.leftDerived n).map φ.τ₂ ≫ (F.leftDerived n).map Q'.g
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂₃]

variable (B' : Type vGlobal) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
  [SMulCommClass R Sᵐᵒᵖ B']
  (f : B →ₗ[R] B') (hf : ∀ (sGlobal : Sᵐᵒᵖ) (x : B), f (sGlobal • x) = sGlobal • f x)

/-- Native derivation of an original coefficient morphism maps the whole exact window. -/
def originalTorLongSequenceCoefficientMap (n : ℕ)
    (Q : ShortComplex (ModuleCat.{vGlobal} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    LeftDerivedDelta.LDlongSequence (tensorFunctor R S B) n Q hQ ⟶
      LeftDerivedDelta.LDlongSequence (tensorFunctor R S B') n Q hQ := by
  let α := torCoefficientTransformation R S B B' f hf (n + 1)
  let β := torCoefficientTransformation R S B B' f hf n
  refine ComposableArrows.homMk₅ (α.app Q.X₁) (α.app Q.X₂) (α.app Q.X₃)
    (β.app Q.X₁) (β.app Q.X₂) (β.app Q.X₃) ?_ ?_ ?_ ?_ ?_
  · exact α.naturality Q.f
  · exact α.naturality Q.g
  · exact (LeftDerivedDelta.LDdelta_natural_functor
      (tensorCoefficientTransformation R S B B' f hf) n Q hQ).symm
  · exact β.naturality Q.f
  · exact β.naturality Q.g

end OriginalWindows

section ProjectiveLift

variable [HasProjectiveResolutions (ModuleCat.{vGlobal} Rᵐᵒᵖ)]
  [(ModuleCat.uliftFunctor.{max rGlobal vGlobal zGlobal, vGlobal} Rᵐᵒᵖ).PreservesProjectiveObjects]

/-- Actual source capabilities compare original Tor with Tor derived in the larger universe. -/
def torOriginalWorldIsoAt.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type v) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
    [(ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ).PreservesProjectiveObjects] (n : ℕ) :
    torFunctor R S B n ⋙ ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ ≅
      torFunctorAt.{z, r, s, v, v} R S B n := by
  letI : HasProjectiveResolutions (ModuleCat.{max r v z} Rᵐᵒᵖ) := inferInstance
  let F := tensorFunctor R S B
  let G := largeTensorFunctorAt.{z, r, s, v, v} R S B
  let U := ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ
  letI : U.PreservesHomology := Functor.preservesHomologyOfExact U
  letI : V.PreservesHomology := Functor.preservesHomologyOfExact V
  exact Functor.leftDerivedTransportIso U V F G
    (tensorOriginalLiftIsoAt.{z, r, s, v} R S B) n


/-- The hom is the actual postcomposition, tensor and source-precomposition factorization. -/
theorem torOriginalWorldIsoAt_hom.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type v) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
    [(ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ).PreservesProjectiveObjects] (n : ℕ) :
    letI : HasProjectiveResolutions (ModuleCat.{max r v z} Rᵐᵒᵖ) := inferInstance
    let F := tensorFunctor R S B
    let G := largeTensorFunctorAt.{z, r, s, v, v} R S B
    let U := ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ
    let V := ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ
    letI : U.PreservesHomology := Functor.preservesHomologyOfExact U
    letI : V.PreservesHomology := Functor.preservesHomologyOfExact V
    (torOriginalWorldIsoAt.{z, r, s, v} R S B n).hom =
      (F.leftDerivedCompIsoOfPreservesHomology V n).hom ≫
        (NatIso.leftDerived (tensorOriginalLiftIsoAt R S B).symm n).hom ≫
          (Functor.leftDerivedPrecompIso U G n).hom := rfl

/-- The comparison preserves the canonical augmentation and the actual original tensor. -/
theorem torOriginalWorldIsoAt_hom_zero.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type v) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
    [(ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ).PreservesProjectiveObjects] :
    (torOriginalWorldIsoAt.{z, r, s, v} R S B 0).hom ≫
        (torZeroIsoAt.{z, r, s, v, v} R S B).hom ≫
          (tensorOriginalLiftIsoAt.{z, r, s, v} R S B).hom =
      Functor.whiskerRight (torZeroIso R S B).hom
        (ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ) := by
  let : HasProjectiveResolutions (ModuleCat.{max r v z} Rᵐᵒᵖ) := inferInstance
  let F := tensorFunctor R S B
  let G := largeTensorFunctorAt.{z, r, s, v, v} R S B
  let U := ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ
  let : U.PreservesHomology := Functor.preservesHomologyOfExact U
  let : V.PreservesHomology := Functor.preservesHomologyOfExact V
  let e := tensorOriginalLiftIsoAt.{z, r, s, v} R S B
  change (Functor.leftDerivedTransportIso U V F G e 0).hom ≫
    Functor.whiskerLeft U G.fromLeftDerivedZero ≫ e.hom = Functor.whiskerRight F.fromLeftDerivedZero V
  have h := congrArg (fun α => α ≫ e.hom)
    (Functor.leftDerivedTransportIso_hom_fromLeftDerivedZero U V F G e)
  exact (Category.assoc (Functor.leftDerivedTransportIso U V F G e 0).hom
      (Functor.whiskerLeft U G.fromLeftDerivedZero) e.hom).symm.trans
    (h.trans ((Category.assoc (Functor.whiskerRight F.fromLeftDerivedZero V) e.inv e.hom).trans
      ((congrArg (fun α => Functor.whiskerRight F.fromLeftDerivedZero V ≫ α) e.inv_hom_id).trans
        (Category.comp_id _))))


/-- Source capabilities suffice for the comparison of the actual connecting morphisms. -/
theorem torOriginalWorldIsoAt_hom_delta.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type v) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
    [(ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ).PreservesProjectiveObjects] (n : ℕ)
    (Q : ShortComplex (ModuleCat.{v} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    (torOriginalWorldIsoAt.{z, r, s, v} R S B (n + 1)).hom.app Q.X₃ ≫
        torDeltaAt.{z, r, s, v, v} R S B n Q hQ =
      (ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ).map
        (LeftDerivedDelta.LDdelta (tensorFunctor R S B) n Q hQ) ≫
          (torOriginalWorldIsoAt.{z, r, s, v} R S B n).hom.app Q.X₁ := by
  let : HasProjectiveResolutions (ModuleCat.{max r v z} Rᵐᵒᵖ) := inferInstance
  let F := tensorFunctor R S B
  let G := largeTensorFunctorAt.{z, r, s, v, v} R S B
  let U := ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ
  let : U.PreservesHomology := Functor.preservesHomologyOfExact U
  let : V.PreservesHomology := Functor.preservesHomologyOfExact V
  let e := tensorOriginalLiftIsoAt.{z, r, s, v} R S B
  exact Functor.leftDerivedTransportIso_hom_LDdelta U V F G e n Q hQ


/-- The whole original exact window is compared using these same six object isomorphisms. -/
def torOriginalWorldLongSequenceIsoAt.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type v) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
    [(ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ).PreservesProjectiveObjects] (n : ℕ)
    (Q : ShortComplex (ModuleCat.{v} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    LeftDerivedDelta.LDlongSequence (tensorFunctor R S B) n Q hQ ⋙
        ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ ≅
      torLongSequenceAt.{z, r, s, v, v} R S B n Q hQ := by
  let α := torOriginalWorldIsoAt.{z, r, s, v} R S B (n + 1)
  let β := torOriginalWorldIsoAt.{z, r, s, v} R S B n
  refine ComposableArrows.isoMk₅ (α.app Q.X₁) (α.app Q.X₂) (α.app Q.X₃)
    (β.app Q.X₁) (β.app Q.X₂) (β.app Q.X₃) ?_ ?_ ?_ ?_ ?_
  · exact α.hom.naturality Q.f
  · exact α.hom.naturality Q.g
  · exact (torOriginalWorldIsoAt_hom_delta R S B n Q hQ).symm
  · exact β.hom.naturality Q.f
  · exact β.hom.naturality Q.g

/-- The original boundary followed by the original tensor augmentation has the same value. -/
theorem torOriginalWorldBoundaryToTensorAt.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type v) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
    [(ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ).PreservesProjectiveObjects]
    (Q : ShortComplex (ModuleCat.{v} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    (torOriginalWorldIsoAt.{z, r, s, v} R S B 1).hom.app Q.X₃ ≫
        torBoundaryToTensorAt.{z, r, s, v, v} R S B Q hQ ≫
          (tensorOriginalLiftIsoAt.{z, r, s, v} R S B).hom.app Q.X₁ =
      (ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ).map
        (LeftDerivedDelta.LDdelta (tensorFunctor R S B) 0 Q hQ ≫
          (torZeroIso R S B).hom.app Q.X₁) := by
  let V := ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ
  have hDelta := torOriginalWorldIsoAt_hom_delta.{z, r, s, v} R S B 0 Q hQ
  have hZero := congrArg (fun α => α.app Q.X₁)
    (torOriginalWorldIsoAt_hom_zero.{z, r, s, v} R S B)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hZero
  unfold torBoundaryToTensorAt
  let α := (torOriginalWorldIsoAt.{z, r, s, v} R S B 1).hom.app Q.X₃
  let δ := torDeltaAt.{z, r, s, v, v} R S B 0 Q hQ
  let ε := (torOriginalWorldIsoAt.{z, r, s, v} R S B 0).hom.app Q.X₁
  let q := (torZeroIsoAt.{z, r, s, v, v} R S B).hom.app Q.X₁
  let e := (tensorOriginalLiftIsoAt.{z, r, s, v} R S B).hom.app Q.X₁
  let d := V.map (LeftDerivedDelta.LDdelta (tensorFunctor R S B) 0 Q hQ)
  change α ≫ (δ ≫ q) ≫ e = _
  have hΔ : α ≫ δ = d ≫ ε := hDelta
  have h₀ : (ε ≫ q) ≫ e = V.map ((torZeroIso R S B).hom.app Q.X₁) := hZero
  exact (congrArg (fun f => f ≫ e) (Category.assoc α δ q).symm).trans
    ((congrArg (fun f => (f ≫ q) ≫ e) hΔ).trans
      ((congrArg (fun f => f ≫ e) (Category.assoc d ε q)).trans
        ((Category.assoc d (ε ≫ q) e).trans
          ((congrArg (fun f => d ≫ f) h₀).trans (V.map_comp _ _).symm))))

/-- Maps of original short exact sequences commute with the whole window comparison. -/
theorem torOriginalWorldLongSequenceIsoAt_natural_sequence.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type v) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
    [(ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ).PreservesProjectiveObjects] (n : ℕ)
    (Q Q' : ShortComplex (ModuleCat.{v} Rᵐᵒᵖ)) (φ : Q ⟶ Q')
    (hQ : Q.ShortExact) (hQ' : Q'.ShortExact) :
    Functor.whiskerRight (originalTorLongSequenceMap R S B n Q Q' φ hQ hQ')
        (ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ) ≫
          (torOriginalWorldLongSequenceIsoAt.{z, r, s, v} R S B n Q' hQ').hom =
      (torOriginalWorldLongSequenceIsoAt.{z, r, s, v} R S B n Q hQ).hom ≫
        torLongSequenceMapAt.{z, r, s, v, v} R S B n Q Q' φ hQ hQ' := by
  apply ComposableArrows.hom_ext₅
  · exact (torOriginalWorldIsoAt R S B (n + 1)).hom.naturality φ.τ₁
  · exact (torOriginalWorldIsoAt R S B (n + 1)).hom.naturality φ.τ₂
  · exact (torOriginalWorldIsoAt R S B (n + 1)).hom.naturality φ.τ₃
  · exact (torOriginalWorldIsoAt R S B n).hom.naturality φ.τ₁
  · exact (torOriginalWorldIsoAt R S B n).hom.naturality φ.τ₂
  · exact (torOriginalWorldIsoAt R S B n).hom.naturality φ.τ₃

section Coefficients

variable (B' : Type vGlobal) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
  [SMulCommClass R Sᵐᵒᵖ B']
  (f : B →ₗ[R] B') (hf : ∀ (sGlobal : Sᵐᵒᵖ) (x : B), f (sGlobal • x) = sGlobal • f x)

/-- The comparison is natural in the actual original coefficient morphism. -/
theorem torOriginalWorldIsoAt_natural_coefficient.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type v) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type v) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B'] (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
    [(ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ).PreservesProjectiveObjects] (n : ℕ) :
    Functor.whiskerRight (torCoefficientTransformation R S B B' f hf n)
        (ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ) ≫
          (torOriginalWorldIsoAt.{z, r, s, v} R S B' n).hom =
      (torOriginalWorldIsoAt.{z, r, s, v} R S B n).hom ≫
        torCoefficientTransformationAt.{z, r, s, v, v} R S B B' f hf n := by
  let : HasProjectiveResolutions (ModuleCat.{max r v z} Rᵐᵒᵖ) := inferInstance
  let F := tensorFunctor R S B
  let G := largeTensorFunctorAt.{z, r, s, v, v} R S B
  let U := ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ
  let : U.PreservesHomology := Functor.preservesHomologyOfExact U
  let : V.PreservesHomology := Functor.preservesHomologyOfExact V
  let e := tensorOriginalLiftIsoAt.{z, r, s, v} R S B
  let F' := tensorFunctor R S B'
  let G' := largeTensorFunctorAt.{z, r, s, v, v} R S B'
  let α := tensorCoefficientTransformation R S B B' f hf
  let β := largeTensorCoefficientTransformationAt.{z, r, s, v, v} R S B B' f hf
  let e' := tensorOriginalLiftIsoAt.{z, r, s, v} R S B'
  exact Functor.leftDerivedTransportIso_naturality U V F G e α β e'
    (tensorOriginalLiftIsoAt_natural_coefficient R S B B' f hf) n


/-- Actual coefficient morphisms commute with the original-world exact-window comparison. -/
theorem torOriginalWorldLongSequenceIsoAt_natural_coefficient.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type v) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type v) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B'] (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
    [(ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ).PreservesProjectiveObjects] (n : ℕ)
    (Q : ShortComplex (ModuleCat.{v} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    Functor.whiskerRight (originalTorLongSequenceCoefficientMap R S B B' f hf n Q hQ)
        (ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ) ≫
          (torOriginalWorldLongSequenceIsoAt.{z, r, s, v} R S B' n Q hQ).hom =
      (torOriginalWorldLongSequenceIsoAt.{z, r, s, v} R S B n Q hQ).hom ≫
        torLongSequenceCoefficientMapAt.{z, r, s, v, v} R S B B' f hf n Q hQ := by
  have h (m : ℕ) (X : ModuleCat.{v} Rᵐᵒᵖ) :
      (ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ).map
          ((torCoefficientTransformation R S B B' f hf m).app X) ≫
        (torOriginalWorldIsoAt R S B' m).hom.app X =
      (torOriginalWorldIsoAt R S B m).hom.app X ≫
        (torCoefficientTransformationAt R S B B' f hf m).app X := by
    have h' := congrArg (fun α => α.app X)
      (torOriginalWorldIsoAt_natural_coefficient R S B B' f hf m)
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app] using h'
  apply ComposableArrows.hom_ext₅
  · exact h (n + 1) Q.X₁
  · exact h (n + 1) Q.X₂
  · exact h (n + 1) Q.X₃
  · exact h n Q.X₁
  · exact h n Q.X₂
  · exact h n Q.X₃

end Coefficients
end ProjectiveLift
end ModuleCat.BalancedTensorRight
