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
# Tor comparisons after enlarging the module universe

Let `R : Type r` and `S : Type s` be associative rings and `B : Type v` an `R`-left, `S`-right
bimodule. Put `λ = max r v z`. Assume `ModuleCat.{v} Rᵐᵒᵖ` has projective resolutions and its
lift to carrier universe `λ` preserves projective objects.

Tor computed in the source module category, followed by lifting the right `S`-module output,
is naturally isomorphic to the larger-universe Tor construction on the lifted inputs and
coefficient. The comparison combines exact target lifting, the tensor coordinate isomorphism,
and source lifting. It respects the degree-zero tensor augmentation and the connecting
morphisms.

These isomorphisms compare the six-term Tor windows of short exact sequences and commute with
maps of such sequences and bimodule coefficients. The unlifted windows also have their derived
sequence and coefficient maps. The ring, outer ring, coefficient, and auxiliary lift universes
remain independent.
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

/-- Lifted tensor comparison is natural in bimodule coefficients.

For an `R`-linear coefficient map `f : B → B'` preserving the right `S`-action, the tensor
coefficient transformation in the larger universe followed by the target tensor comparison
equals the source tensor comparison followed by lifting the unlifted coefficient
transformation. -/
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

/-- Map of source-universe Tor windows from a short-complex morphism.

Assume projective resolutions for right `R`-modules in the source carrier universe. A morphism
`φ : Q ⟶ Q'` between short exact complexes induces a morphism of their six-term Tor windows in
degrees `n + 1` and `n`, with the derived maps on the three objects in each degree. -/
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

/-- Bimodule coefficient map on a source-universe Tor window.

Assuming source projective resolutions, an `R`-linear coefficient map preserving the right
`S`-action induces a morphism between the six-term Tor windows for `B` and `B'` at a fixed
short exact sequence. -/
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

/-- Source Tor after output lifting as larger-universe Tor.

Put `λ = max r v z`. If the source right-module category has projective resolutions and
`ModuleCat.uliftFunctor.{λ,v} Rᵐᵒᵖ` preserves projective objects, then `torFunctor R S B n`
followed by lifting the right `S`-module output is naturally isomorphic to
`torFunctorAt.{z,r,s,v,v} R S B n`. -/
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


/-- Factorization of the Tor comparison across module universes.

Under the source resolution and projective-lift assumptions, the forward comparison is the
derived exact-target-lift isomorphism, followed by left derivation of the inverse tensor
comparison, followed by the source-precomposition isomorphism for the projective-preserving
lift. -/
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

/-- Universe comparison respects the degree-zero Tor augmentation.

Under the source resolution and projective-lift assumptions, the degree-zero Tor comparison
followed by the larger-universe zero-Tor and tensor coordinates equals the lifted source
degree-zero augmentation. -/
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


/-- Universe comparison commutes with the Tor connecting morphism.

For a short exact complex `Q`, compare `Tor_(n+1)(Q.X₃)` and `Tor_n(Q.X₁)` across the module
universes. The larger connecting morphism after the degree-`n + 1` comparison equals the
lifted source connecting morphism followed by the degree-`n` comparison, under the source
resolution and projective-lift assumptions. -/
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


/-- Isomorphism of Tor windows across module universes.

Assume source projective resolutions and that the source right-module lift to `λ = max r v z`
preserves projective objects. For a short exact sequence `Q`, the lifted six-term source Tor
window in degrees `n + 1` and `n` is isomorphic to the larger-universe Tor window. -/
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

/-- Universe comparison respects the Tor-one boundary into tensor.

Under the source resolution and projective-lift assumptions, the map from larger-universe
`Tor₁(Q.X₃)` to the tensor object at `Q.X₁`, transported by the Tor and tensor comparison
coordinates, equals the lift of the source connecting morphism in degree zero followed by its
zero-Tor isomorphism. -/
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

/-- Tor-window universe comparison is natural in short exact sequences.

For a morphism between short exact complexes `Q` and `Q'`, the lifted source Tor-window map
followed by the comparison for `Q'` equals the comparison for `Q` followed by the larger-
universe window map. The source projective-resolution and projective-lift assumptions are
retained. -/
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

/-- Tor universe comparison is natural in a bimodule coefficient map.

Under the source resolution and projective-lift assumptions, an `R`-linear coefficient map
preserving the right `S`-action commutes with the degree-`n` Tor comparison. Lift the source
coefficient transformation and compare with its larger-universe transformation. -/
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


/-- Tor-window universe comparison is natural in coefficients.

For a fixed short exact sequence and a compatible map `B → B'`, the lifted source coefficient
map of Tor windows followed by the comparison for `B'` equals the comparison for `B` followed
by the larger-universe coefficient window map, under the source resolution and projective-lift
assumptions. -/
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
