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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.UniverseNaturality
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.TransportComparison
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ParameterMap
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.HorseshoeBoundaryChoice
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.BoundaryIsomorphism

/-!
# Long exact Tor windows for independently sized right-module sequences

Let R,S be rings, B an (R,S)-bimodule and
Q₁→Q₂→Q₃ a short exact sequence of right R-modules in world a.
At Γ_z=max(r,a,b,z), exact source lifting gives a short exact
sequence in the category where source-derived Tor is computed.

For n≥0 the five-arrow window is
Tor_(n+1)(Q₁,B)→Tor_(n+1)(Q₂,B)→Tor_(n+1)(Q₃,B)
→δ_n Tor_n(Q₁,B)→Tor_n(Q₂,B)→Tor_n(Q₃,B).
It is exact in right S-modules at height Γ_z.
The boundary and entire window are natural in sequence morphisms
and in R-linear right S-equivariant coefficient maps.

Increasing the height preserves all six objects and all five maps.
The degree-one boundary followed by Tor_0≅tensor gives the
boundary Tor_1(Q₃,B)→Q₁⊗_R B in the lifted tensor model.
Two heights are compared in one common output height.
An unlifted common-world comparison additionally assumes R small
in that source world; no smallness condition is imposed on S.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe zGlobal tGlobal rGlobal sGlobal aGlobal bGlobal
namespace ModuleCat.BalancedTensorRight
variable (R : Type rGlobal) (S : Type sGlobal) [Ring R] [Ring S]
  (B : Type bGlobal) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
  [SMulCommClass R Sᵐᵒᵖ B]

/-- For a short complex Q of right R-modules in world a,
lifting its three objects and two maps to
Γ_z=max(r,a,b,z) gives the corresponding short complex
in ModuleCat^Γ_z(Rᵒᵖ).
Exactness and the short exact property are preserved by this lift. -/
abbrev liftedShortComplexAt.{z, r, a, b} (R : Type r) [Ring R]
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) :
    ShortComplex (ModuleCat.{max r a b z} Rᵐᵒᵖ) :=
  Q.map (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)

/-- For an (R,S)-bimodule B, a short exact sequence
Q₁→Q₂→Q₃ of right R-modules and n≥0, the connecting map is
δ_n:Tor_(n+1,z)(Q₃,B)→Tor_(n,z)(Q₁,B).
It is formed after exact source lifting to Γ_z=max(r,a,b,z). -/
def torDeltaAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ)
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    torObjAt.{z, r, s, a, b} R S B (n + 1) Q.X₃ ⟶
      torObjAt.{z, r, s, a, b} R S B n Q.X₁ := by
  letI : HasProjectiveResolutions (ModuleCat.{max r a b z} Rᵐᵒᵖ) := inferInstance
  exact LeftDerivedDelta.LDdelta (largeTensorFunctorAt.{z, r, s, a, b} R S B) n
    (liftedShortComplexAt.{z, r, a, b} R Q)
    (hQ.map_of_exact (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ))

/-- For an (R,S)-bimodule B and a short exact right R-module
sequence Q, the degree-n window consists of the three
Tor_(n+1,z)(Q_i,B) terms, the connecting map δ_n, and the
three Tor_(n,z)(Q_i,B) terms in that order.
All six objects are right S-modules in world Γ_z. -/
def torLongSequenceAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ)
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    ComposableArrows (ModuleCat.{max r a b z} Sᵐᵒᵖ) 5 := by
  letI : HasProjectiveResolutions (ModuleCat.{max r a b z} Rᵐᵒᵖ) := inferInstance
  exact LeftDerivedDelta.LDlongSequence (largeTensorFunctorAt.{z, r, s, a, b} R S B) n
    (liftedShortComplexAt.{z, r, a, b} R Q)
    (hQ.map_of_exact (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ))

/-- For rings R,S, an (R,S)-bimodule B and a short exact
right R-module sequence Q, the five-arrow window across
degrees n+1 and n is exact for every n≥0.
The only sequence exactness premise is the short exact property of Q. -/
theorem torLongSequenceAt_exact.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ)
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    (torLongSequenceAt.{z, r, s, a, b} R S B n Q hQ).Exact := by
  letI : HasProjectiveResolutions (ModuleCat.{max r a b z} Rᵐᵒᵖ) := inferInstance
  exact LeftDerivedDelta.LDlongSequence_exact
    (largeTensorFunctorAt.{z, r, s, a, b} R S B) n
    (liftedShortComplexAt.{z, r, a, b} R Q)
    (hQ.map_of_exact (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ))

/-- For a morphism φ:Q→Q′ of short exact right R-module
sequences, the boundaries satisfy
δ_(Q′,n)∘Tor_(n+1,z)(φ₃)=Tor_(n,z)(φ₁)∘δ_(Q,n).
The coefficient is a fixed (R,S)-bimodule B. -/
theorem torDeltaAt_natural_sequence.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ)
    (Q Q' : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (φ : Q ⟶ Q')
    (hQ : Q.ShortExact) (hQ' : Q'.ShortExact) :
    torMapAt.{z, r, s, a, b} R S B (n + 1) φ.τ₃ ≫
        torDeltaAt.{z, r, s, a, b} R S B n Q' hQ' =
      torDeltaAt.{z, r, s, a, b} R S B n Q hQ ≫ torMapAt.{z, r, s, a, b} R S B n φ.τ₁ := by
  let U := ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ
  exact LeftDerivedDelta.LDdelta_natural
    (largeTensorFunctorAt.{z, r, s, a, b} R S B) n
    (Q'.map U) (Q.map U) (U.mapShortComplex.map φ)
    (hQ'.map_of_exact U) (hQ.map_of_exact U)

/-- For an (R,S)-bimodule B and a map φ:Q→Q′ of short exact
right R-module sequences, the six component Tor maps give a
morphism between their five-arrow windows.
The central square is the naturality of δ_n. -/
def torLongSequenceMapAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ)
    (Q Q' : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (φ : Q ⟶ Q')
    (hQ : Q.ShortExact) (hQ' : Q'.ShortExact) :
    torLongSequenceAt.{z, r, s, a, b} R S B n Q hQ ⟶
      torLongSequenceAt.{z, r, s, a, b} R S B n Q' hQ' := by
  refine ComposableArrows.homMk₅
    (torMapAt.{z, r, s, a, b} R S B (n + 1) φ.τ₁)
    (torMapAt.{z, r, s, a, b} R S B (n + 1) φ.τ₂)
    (torMapAt.{z, r, s, a, b} R S B (n + 1) φ.τ₃)
    (torMapAt.{z, r, s, a, b} R S B n φ.τ₁)
    (torMapAt.{z, r, s, a, b} R S B n φ.τ₂)
    (torMapAt.{z, r, s, a, b} R S B n φ.τ₃) ?_ ?_ ?_ ?_ ?_
  · change (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map Q.f ≫
        (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map φ.τ₂ =
      (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map φ.τ₁ ≫
        (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map Q'.f
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁₂]
  · change (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map Q.g ≫
        (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map φ.τ₃ =
      (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map φ.τ₂ ≫
        (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map Q'.g
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂₃]
  · exact (torDeltaAt_natural_sequence R S B n Q Q' φ hQ hQ').symm
  · change (torFunctorAt.{z, r, s, a, b} R S B n).map Q.f ≫ (torFunctorAt.{z, r, s, a, b} R S B n).map φ.τ₂ =
      (torFunctorAt.{z, r, s, a, b} R S B n).map φ.τ₁ ≫ (torFunctorAt.{z, r, s, a, b} R S B n).map Q'.f
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁₂]
  · change (torFunctorAt.{z, r, s, a, b} R S B n).map Q.g ≫ (torFunctorAt.{z, r, s, a, b} R S B n).map φ.τ₃ =
      (torFunctorAt.{z, r, s, a, b} R S B n).map φ.τ₂ ≫ (torFunctorAt.{z, r, s, a, b} R S B n).map Q'.g
    rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂₃]

/-- For a ring R and source world a, the objects are short
exact short complexes in ModuleCat^a(Rᵒᵖ), with morphisms
the commuting maps of their three terms.
This is the source category for the long exact Tor-window functor. -/
abbrev torShortExactCategoryAt :=
  (show ObjectProperty (ShortComplex (ModuleCat.{aGlobal} Rᵐᵒᵖ)) from
    fun Q => Q.ShortExact).FullSubcategory

/-- For rings R,S, an (R,S)-bimodule B and n≥0, assigning
the five-arrow Tor window to a short exact right R-module
sequence is a functor into ComposableArrows(ModuleCat^Γ_z(Sᵒᵖ),5).
The source sequences retain their carrier world a. -/
def torLongSequenceFunctorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    torShortExactCategoryAt (R := R) ⥤
      ComposableArrows (ModuleCat.{max r a b z} Sᵐᵒᵖ) 5 where
  obj Q := torLongSequenceAt.{z, r, s, a, b} R S B n Q.obj Q.property
  map φ := torLongSequenceMapAt.{z, r, s, a, b} R S B n _ _ φ.hom _ _
  map_id Q := by
    apply ComposableArrows.hom_ext₅
    · change (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map (𝟙 Q.obj.X₁) = 𝟙 _
      exact (torFunctorAt.{z, r, s, a, b} R S B _).map_id _
    · change (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map (𝟙 Q.obj.X₂) = 𝟙 _
      exact (torFunctorAt.{z, r, s, a, b} R S B _).map_id _
    · change (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map (𝟙 Q.obj.X₃) = 𝟙 _
      exact (torFunctorAt.{z, r, s, a, b} R S B _).map_id _
    · change (torFunctorAt.{z, r, s, a, b} R S B n).map (𝟙 Q.obj.X₁) = 𝟙 _
      exact (torFunctorAt.{z, r, s, a, b} R S B _).map_id _
    · change (torFunctorAt.{z, r, s, a, b} R S B n).map (𝟙 Q.obj.X₂) = 𝟙 _
      exact (torFunctorAt.{z, r, s, a, b} R S B _).map_id _
    · change (torFunctorAt.{z, r, s, a, b} R S B n).map (𝟙 Q.obj.X₃) = 𝟙 _
      exact (torFunctorAt.{z, r, s, a, b} R S B _).map_id _
  map_comp {Q Q' Q''} φ ψ := by
    apply ComposableArrows.hom_ext₅
    · change (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map (φ.hom.τ₁ ≫ ψ.hom.τ₁) =
        (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map φ.hom.τ₁ ≫
          (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map ψ.hom.τ₁
      exact (torFunctorAt.{z, r, s, a, b} R S B _).map_comp _ _
    · change (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map (φ.hom.τ₂ ≫ ψ.hom.τ₂) =
        (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map φ.hom.τ₂ ≫
          (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map ψ.hom.τ₂
      exact (torFunctorAt.{z, r, s, a, b} R S B _).map_comp _ _
    · change (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map (φ.hom.τ₃ ≫ ψ.hom.τ₃) =
        (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map φ.hom.τ₃ ≫
          (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map ψ.hom.τ₃
      exact (torFunctorAt.{z, r, s, a, b} R S B _).map_comp _ _
    · change (torFunctorAt.{z, r, s, a, b} R S B n).map (φ.hom.τ₁ ≫ ψ.hom.τ₁) =
        (torFunctorAt.{z, r, s, a, b} R S B n).map φ.hom.τ₁ ≫ (torFunctorAt.{z, r, s, a, b} R S B n).map ψ.hom.τ₁
      exact (torFunctorAt.{z, r, s, a, b} R S B _).map_comp _ _
    · change (torFunctorAt.{z, r, s, a, b} R S B n).map (φ.hom.τ₂ ≫ ψ.hom.τ₂) =
        (torFunctorAt.{z, r, s, a, b} R S B n).map φ.hom.τ₂ ≫ (torFunctorAt.{z, r, s, a, b} R S B n).map ψ.hom.τ₂
      exact (torFunctorAt.{z, r, s, a, b} R S B _).map_comp _ _
    · change (torFunctorAt.{z, r, s, a, b} R S B n).map (φ.hom.τ₃ ≫ ψ.hom.τ₃) =
        (torFunctorAt.{z, r, s, a, b} R S B n).map φ.hom.τ₃ ≫ (torFunctorAt.{z, r, s, a, b} R S B n).map ψ.hom.τ₃
      exact (torFunctorAt.{z, r, s, a, b} R S B _).map_comp _ _

/-- For an (R,S)-bimodule B and a short exact right R-module
sequence Q, the window morphism induced by id_Q is the
identity on its chosen-height degree-n Tor window. -/
theorem torLongSequenceMapAt_id.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ)
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    torLongSequenceMapAt.{z, r, s, a, b} R S B n Q Q (𝟙 Q) hQ hQ =
      𝟙 (torLongSequenceAt.{z, r, s, a, b} R S B n Q hQ) :=
  (torLongSequenceFunctorAt R S B n).map_id ⟨Q, hQ⟩

/-- For composable morphisms φ:Q→Q′ and ψ:Q′→Q″ of short
exact right R-module sequences, the window map of ψ∘φ is
the window map of φ followed by that of ψ.
The fixed coefficient is an (R,S)-bimodule B. -/
theorem torLongSequenceMapAt_comp.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ)
    (Q Q' Q'' : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ))
    (φ : Q ⟶ Q') (ψ : Q' ⟶ Q'')
    (hQ : Q.ShortExact) (hQ' : Q'.ShortExact) (hQ'' : Q''.ShortExact) :
    torLongSequenceMapAt.{z, r, s, a, b} R S B n Q Q'' (φ ≫ ψ) hQ hQ'' =
      torLongSequenceMapAt.{z, r, s, a, b} R S B n Q Q' φ hQ hQ' ≫
        torLongSequenceMapAt.{z, r, s, a, b} R S B n Q' Q'' ψ hQ' hQ'' :=
  (torLongSequenceFunctorAt R S B n).map_comp
    (ObjectProperty.homMk φ : (⟨Q, hQ⟩ : torShortExactCategoryAt (R := R)) ⟶ ⟨Q', hQ'⟩)
    (ObjectProperty.homMk ψ : (⟨Q', hQ'⟩ : torShortExactCategoryAt (R := R)) ⟶ ⟨Q'', hQ''⟩)

section Coefficients

variable (B' : Type bGlobal) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
  [SMulCommClass R Sᵐᵒᵖ B'] (f : B →ₗ[R] B')
  (hf : ∀ (sGlobal : Sᵐᵒᵖ) (x : B), f (sGlobal • x) = sGlobal • f x)

/-- For an (R,S)-bimodule map f:B→B′ and a short exact
right R-module sequence Q, the coefficient maps commute with
δ_n from Q₃ in degree n+1 to Q₁ in degree n.
Equivariance of f means R-linearity and right S-linearity. -/
theorem torDeltaAt_natural_coefficient.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) (n : ℕ)
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n + 1)).app Q.X₃ ≫
        torDeltaAt.{z, r, s, a, b} R S B' n Q hQ =
      torDeltaAt.{z, r, s, a, b} R S B n Q hQ ≫
        (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf n).app Q.X₁ := by
  let U := ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ
  exact LeftDerivedDelta.LDdelta_natural_functor
    (tensorCoefficientTransformation R S
      (ULift.{max r a b z} B) (ULift.{max r a b z} B')
      (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf))
    n (Q.map U) (hQ.map_of_exact U)

/-- For a bimodule map f:B→B′, a short exact right R-module
sequence Q and n≥0, the six coefficient Tor transformations
give a morphism from the B-window to the B′-window.
They preserve its central connecting map and all sequence maps. -/
def torLongSequenceCoefficientMapAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) (n : ℕ)
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    torLongSequenceAt.{z, r, s, a, b} R S B n Q hQ ⟶
      torLongSequenceAt.{z, r, s, a, b} R S B' n Q hQ := by
  let α := torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n + 1)
  let β := torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf n
  refine ComposableArrows.homMk₅ (α.app Q.X₁) (α.app Q.X₂) (α.app Q.X₃)
    (β.app Q.X₁) (β.app Q.X₂) (β.app Q.X₃) ?_ ?_ ?_ ?_ ?_
  · exact α.naturality Q.f
  · exact α.naturality Q.g
  · exact (torDeltaAt_natural_coefficient R S B B' f hf n Q hQ).symm
  · exact β.naturality Q.f
  · exact β.naturality Q.g


/-- For an (R,S)-bimodule B and a short exact right R-module
sequence Q, id_B induces the identity morphism of the
chosen-height Tor window in every degree n≥0. -/
theorem torLongSequenceCoefficientMapAt_id.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ)
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    torLongSequenceCoefficientMapAt.{z, r, s, a, b} R S B B LinearMap.id
      (fun _ _ => rfl) n Q hQ = 𝟙 (torLongSequenceAt.{z, r, s, a, b} R S B n Q hQ) := by
  apply ComposableArrows.hom_ext₅
  · change (torCoefficientTransformationAt.{z, r, s, a, b} R S B B LinearMap.id (fun _ _ => rfl)
        (n + 1)).app Q.X₁ = 𝟙 _
    exact congrArg (fun α => α.app Q.X₁)
      (torCoefficientTransformationAt_id R S B (n + 1))
  · change (torCoefficientTransformationAt.{z, r, s, a, b} R S B B LinearMap.id (fun _ _ => rfl)
        (n + 1)).app Q.X₂ = 𝟙 _
    exact congrArg (fun α => α.app Q.X₂)
      (torCoefficientTransformationAt_id R S B (n + 1))
  · change (torCoefficientTransformationAt.{z, r, s, a, b} R S B B LinearMap.id (fun _ _ => rfl)
        (n + 1)).app Q.X₃ = 𝟙 _
    exact congrArg (fun α => α.app Q.X₃)
      (torCoefficientTransformationAt_id R S B (n + 1))
  · change (torCoefficientTransformationAt.{z, r, s, a, b} R S B B LinearMap.id (fun _ _ => rfl)
        (n)).app Q.X₁ = 𝟙 _
    exact congrArg (fun α => α.app Q.X₁)
      (torCoefficientTransformationAt_id R S B (n))
  · change (torCoefficientTransformationAt.{z, r, s, a, b} R S B B LinearMap.id (fun _ _ => rfl)
        (n)).app Q.X₂ = 𝟙 _
    exact congrArg (fun α => α.app Q.X₂)
      (torCoefficientTransformationAt_id R S B (n))
  · change (torCoefficientTransformationAt.{z, r, s, a, b} R S B B LinearMap.id (fun _ _ => rfl)
        (n)).app Q.X₃ = 𝟙 _
    exact congrArg (fun α => α.app Q.X₃)
      (torCoefficientTransformationAt_id R S B (n))

variable (B'' : Type bGlobal) [AddCommGroup B''] [Module R B''] [Module Sᵐᵒᵖ B'']
  [SMulCommClass R Sᵐᵒᵖ B''] (g : B' →ₗ[R] B'')
  (hg : ∀ (sGlobal : Sᵐᵒᵖ) (x : B'), g (sGlobal • x) = sGlobal • g x)

/-- For bimodule maps f:B→B′ and g:B′→B″, the window
morphism for g∘f equals the morphism for f followed by that
for g, on every short exact right R-module sequence Q.
All six Tor terms retain this composition order. -/
theorem torLongSequenceCoefficientMapAt_comp.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (B'' : Type b) [AddCommGroup B''] [Module R B''] [Module Sᵐᵒᵖ B'']
    [SMulCommClass R Sᵐᵒᵖ B'']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (g : B' →ₗ[R] B'')
    (hg : ∀ (s : Sᵐᵒᵖ) (x : B'), g (s • x) = s • g x) (n : ℕ)
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    torLongSequenceCoefficientMapAt.{z, r, s, a, b} R S B B' f hf n Q hQ ≫
        torLongSequenceCoefficientMapAt.{z, r, s, a, b} R S B' B'' g hg n Q hQ =
      torLongSequenceCoefficientMapAt.{z, r, s, a, b} R S B B'' (g.comp f)
        (fun s x => (congrArg g (hf s x)).trans (hg s (f x))) n Q hQ := by
  apply ComposableArrows.hom_ext₅
  · change (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n + 1)).app Q.X₁ ≫
        (torCoefficientTransformationAt.{z, r, s, a, b} R S B' B'' g hg (n + 1)).app Q.X₁ =
      (torCoefficientTransformationAt.{z, r, s, a, b} R S B B'' (g.comp f)
        (fun s x => (congrArg g (hf s x)).trans (hg s (f x))) (n + 1)).app Q.X₁
    exact congrArg (fun α => α.app Q.X₁)
      (torCoefficientTransformationAt_comp R S B B' B'' f g hf hg (n + 1))
  · change (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n + 1)).app Q.X₂ ≫
        (torCoefficientTransformationAt.{z, r, s, a, b} R S B' B'' g hg (n + 1)).app Q.X₂ =
      (torCoefficientTransformationAt.{z, r, s, a, b} R S B B'' (g.comp f)
        (fun s x => (congrArg g (hf s x)).trans (hg s (f x))) (n + 1)).app Q.X₂
    exact congrArg (fun α => α.app Q.X₂)
      (torCoefficientTransformationAt_comp R S B B' B'' f g hf hg (n + 1))
  · change (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n + 1)).app Q.X₃ ≫
        (torCoefficientTransformationAt.{z, r, s, a, b} R S B' B'' g hg (n + 1)).app Q.X₃ =
      (torCoefficientTransformationAt.{z, r, s, a, b} R S B B'' (g.comp f)
        (fun s x => (congrArg g (hf s x)).trans (hg s (f x))) (n + 1)).app Q.X₃
    exact congrArg (fun α => α.app Q.X₃)
      (torCoefficientTransformationAt_comp R S B B' B'' f g hf hg (n + 1))
  · change (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n)).app Q.X₁ ≫
        (torCoefficientTransformationAt.{z, r, s, a, b} R S B' B'' g hg (n)).app Q.X₁ =
      (torCoefficientTransformationAt.{z, r, s, a, b} R S B B'' (g.comp f)
        (fun s x => (congrArg g (hf s x)).trans (hg s (f x))) (n)).app Q.X₁
    exact congrArg (fun α => α.app Q.X₁)
      (torCoefficientTransformationAt_comp R S B B' B'' f g hf hg (n))
  · change (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n)).app Q.X₂ ≫
        (torCoefficientTransformationAt.{z, r, s, a, b} R S B' B'' g hg (n)).app Q.X₂ =
      (torCoefficientTransformationAt.{z, r, s, a, b} R S B B'' (g.comp f)
        (fun s x => (congrArg g (hf s x)).trans (hg s (f x))) (n)).app Q.X₂
    exact congrArg (fun α => α.app Q.X₂)
      (torCoefficientTransformationAt_comp R S B B' B'' f g hf hg (n))
  · change (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n)).app Q.X₃ ≫
        (torCoefficientTransformationAt.{z, r, s, a, b} R S B' B'' g hg (n)).app Q.X₃ =
      (torCoefficientTransformationAt.{z, r, s, a, b} R S B B'' (g.comp f)
        (fun s x => (congrArg g (hf s x)).trans (hg s (f x))) (n)).app Q.X₃
    exact congrArg (fun α => α.app Q.X₃)
      (torCoefficientTransformationAt_comp R S B B' B'' f g hf hg (n))

/-- For a short exact sequence morphism φ:Q→Q′ and a
bimodule map f:B→B′, changing the sequence and then the
coefficient gives the same window morphism as changing the
coefficient and then the sequence.
The assertion includes the connecting-map square. -/
theorem torLongSequenceMapAt_coefficient_interchange.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) (n : ℕ)
    (Q Q' : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (φ : Q ⟶ Q')
    (hQ : Q.ShortExact) (hQ' : Q'.ShortExact) :
    torLongSequenceMapAt.{z, r, s, a, b} R S B n Q Q' φ hQ hQ' ≫
        torLongSequenceCoefficientMapAt.{z, r, s, a, b} R S B B' f hf n Q' hQ' =
      torLongSequenceCoefficientMapAt.{z, r, s, a, b} R S B B' f hf n Q hQ ≫
        torLongSequenceMapAt.{z, r, s, a, b} R S B' n Q Q' φ hQ hQ' := by
  apply ComposableArrows.hom_ext₅
  · change (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map φ.τ₁ ≫
        (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n + 1)).app Q'.X₁ =
      (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n + 1)).app Q.X₁ ≫
        (torFunctorAt.{z, r, s, a, b} R S B' (n + 1)).map φ.τ₁
    exact (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n + 1)).naturality φ.τ₁
  · change (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map φ.τ₂ ≫
        (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n + 1)).app Q'.X₂ =
      (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n + 1)).app Q.X₂ ≫
        (torFunctorAt.{z, r, s, a, b} R S B' (n + 1)).map φ.τ₂
    exact (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n + 1)).naturality φ.τ₂
  · change (torFunctorAt.{z, r, s, a, b} R S B (n + 1)).map φ.τ₃ ≫
        (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n + 1)).app Q'.X₃ =
      (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n + 1)).app Q.X₃ ≫
        (torFunctorAt.{z, r, s, a, b} R S B' (n + 1)).map φ.τ₃
    exact (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n + 1)).naturality φ.τ₃
  · change (torFunctorAt.{z, r, s, a, b} R S B (n)).map φ.τ₁ ≫
        (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n)).app Q'.X₁ =
      (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n)).app Q.X₁ ≫
        (torFunctorAt.{z, r, s, a, b} R S B' (n)).map φ.τ₁
    exact (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n)).naturality φ.τ₁
  · change (torFunctorAt.{z, r, s, a, b} R S B (n)).map φ.τ₂ ≫
        (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n)).app Q'.X₂ =
      (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n)).app Q.X₂ ≫
        (torFunctorAt.{z, r, s, a, b} R S B' (n)).map φ.τ₂
    exact (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n)).naturality φ.τ₂
  · change (torFunctorAt.{z, r, s, a, b} R S B (n)).map φ.τ₃ ≫
        (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n)).app Q'.X₃ =
      (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n)).app Q.X₃ ≫
        (torFunctorAt.{z, r, s, a, b} R S B' (n)).map φ.τ₃
    exact (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf (n)).naturality φ.τ₃

end Coefficients

section HeightComparison

/-- For a short exact right R-module sequence Q already in
world Γ_z and an (R,S)-bimodule B, the height comparisons
Γ_z→Γ′=max(r,a,b,z,t) satisfy
δ_(UQ,n)^Γ′∘η_(n+1)(Q₃)=η_n(Q₁)∘U_S(δ_(Q,n)^Γ_z).
Here U is source lifting and U_S is output lifting. -/
theorem largeTorHeightIsoAt_hom_LDdelta.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (n : ℕ) (Q : ShortComplex (ModuleCat.{max r a b z} Rᵐᵒᵖ))
    (hQ : Q.ShortExact) :
    let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
    (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B (n + 1)).hom.app Q.X₃ ≫
        LeftDerivedDelta.LDdelta
          (largeTensorFunctorAt.{max z t, r, s, a, b} R S B) n (Q.map U)
          (hQ.map_of_exact U) =
      (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ).map
        (LeftDerivedDelta.LDdelta (largeTensorFunctorAt.{z, r, s, a, b} R S B) n Q hQ) ≫
          (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B n).hom.app Q.X₁ := by
  let F := largeTensorFunctorAt.{z, r, s, a, b} R S B
  let G := largeTensorFunctorAt.{max z t, r, s, a, b} R S B
  let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
  let : U.PreservesHomology := Functor.preservesHomologyOfExact U
  let : V.PreservesHomology := Functor.preservesHomologyOfExact V
  let : U.PreservesProjectiveObjects := inferInstance
  exact Functor.leftDerivedTransportIso_hom_LDdelta U V F G
    (tensorHeightIsoAt.{t, z, r, s, a, b} R S B) n Q hQ


/-- For a short exact right R-module sequence Q in world a,
an (R,S)-bimodule B and n≥0, the height maps Γ_z→Γ′ satisfy
δ_n^Γ′∘η_(n+1)(Q₃)=η_n(Q₁)∘U_S(δ_n^Γ_z).
The original source sequence is the same on both sides. -/
theorem torHeightIsoAt_hom_delta.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ)
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    (torHeightIsoAt.{t, z, r, s, a, b} R S B (n + 1)).hom.app Q.X₃ ≫
        torDeltaAt.{max z t, r, s, a, b} R S B n Q hQ =
      (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ).map
          (torDeltaAt.{z, r, s, a, b} R S B n Q hQ) ≫
        (torHeightIsoAt.{t, z, r, s, a, b} R S B n).hom.app Q.X₁ := by
  let A := ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ
  let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
  let W := ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
  let F := largeTensorFunctorAt.{z, r, s, a, b} R S B
  let G := largeTensorFunctorAt.{max z t, r, s, a, b} R S B
  let ε := ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ
  let φ : (Q.map A).map U ⟶ Q.map W := Q.mapNatTrans ε.hom
  let hLow := hQ.map_of_exact A
  let hDouble := hLow.map_of_exact U
  let hHigh := hQ.map_of_exact W
  let dLow := LeftDerivedDelta.LDdelta F n (Q.map A) hLow
  let dDouble := LeftDerivedDelta.LDdelta G n ((Q.map A).map U) hDouble
  let dHigh := LeftDerivedDelta.LDdelta G n (Q.map W) hHigh
  let β₃ := (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B (n + 1)).hom.app (A.obj Q.X₃)
  let β₁ := (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B n).hom.app (A.obj Q.X₁)
  let f₃ := (G.leftDerived (n + 1)).map (ε.hom.app Q.X₃)
  let f₁ := (G.leftDerived n).map (ε.hom.app Q.X₁)
  have hFirst : β₃ ≫ dDouble = V.map dLow ≫ β₁ :=
    largeTorHeightIsoAt_hom_LDdelta.{t, z, r, s, a, b} R S B n (Q.map A) hLow
  have hLast : f₃ ≫ dHigh = dDouble ≫ f₁ :=
    LeftDerivedDelta.LDdelta_natural G n (Q.map W) ((Q.map A).map U)
      φ hHigh hDouble
  rw [torHeightIsoAt_hom_app, torHeightIsoAt_hom_app]
  change (β₃ ≫ f₃) ≫ dHigh = V.map dLow ≫ (β₁ ≫ f₁)
  exact (Category.assoc β₃ f₃ dHigh).trans
    ((congrArg (fun f => β₃ ≫ f) hLast).trans
      ((Category.assoc β₃ dDouble f₁).symm.trans
        ((congrArg (fun f => f ≫ f₁) hFirst).trans (Category.assoc (V.map dLow) β₁ f₁))))

/-- For an (R,S)-bimodule B and a short exact right R-module
sequence Q, lifting its height-Γ_z Tor window to Γ′ gives
an isomorphism with the window constructed at Γ′.
Its six components are the Tor height comparisons in degrees
n+1 and n. -/
def torLongSequenceHeightIsoAt.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ)
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    torLongSequenceAt.{z, r, s, a, b} R S B n Q hQ ⋙
        ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ ≅
      torLongSequenceAt.{max z t, r, s, a, b} R S B n Q hQ := by
  let α := torHeightIsoAt.{t, z, r, s, a, b} R S B (n + 1)
  let β := torHeightIsoAt.{t, z, r, s, a, b} R S B n
  refine ComposableArrows.isoMk₅ (α.app Q.X₁) (α.app Q.X₂) (α.app Q.X₃)
    (β.app Q.X₁) (β.app Q.X₂) (β.app Q.X₃) ?_ ?_ ?_ ?_ ?_
  · exact α.hom.naturality Q.f
  · exact α.hom.naturality Q.g
  · exact (torHeightIsoAt_hom_delta R S B n Q hQ).symm
  · exact β.hom.naturality Q.f
  · exact β.hom.naturality Q.g

/-- For an (R,S)-bimodule B and a short exact right R-module
sequence Q, the boundary
Tor_(1,z)(Q₃,B)→Tensor_z(Q₁,B)
is δ_0 followed by the canonical Tor_0-to-tensor isomorphism.
It lands in the balanced product of the lifted Q₁ and B carriers. -/
def torBoundaryToTensorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    torObjAt.{z, r, s, a, b} R S B 1 Q.X₃ ⟶
      tensorObjAt.{z, r, s, a, b} R S B Q.X₁ :=
  torDeltaAt.{z, r, s, a, b} R S B 0 Q hQ ≫ (torZeroIsoAt R S B).hom.app Q.X₁

/-- For a bimodule map f:B→B′ and a short exact right
R-module sequence Q, the degree-one Tor coefficient map
commutes with the boundary into Tensor_z(Q₁,−).
The target square uses the underived coefficient tensor map. -/
theorem torBoundaryToTensorAt_natural_coefficient.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B'] (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf 1).app Q.X₃ ≫
        torBoundaryToTensorAt R S B' Q hQ =
      torBoundaryToTensorAt R S B Q hQ ≫
        (tensorCoefficientTransformationAt R S B B' f hf).app Q.X₁ := by
  have hDelta := torDeltaAt_natural_coefficient R S B B' f hf 0 Q hQ
  have hZero := congrArg (fun α => α.app Q.X₁)
    (torZeroIsoAt_naturality_coefficient.{z, r, s, a, b} R S B B' f hf)
  simp only [NatTrans.comp_app] at hZero
  unfold torBoundaryToTensorAt
  calc
    _ = (torDeltaAt.{z, r, s, a, b} R S B 0 Q hQ ≫
        (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf 0).app Q.X₁) ≫
      (torZeroIsoAt R S B').hom.app Q.X₁ := by rw [← Category.assoc, hDelta]
    _ = torDeltaAt.{z, r, s, a, b} R S B 0 Q hQ ≫
      ((torZeroIsoAt R S B).hom.app Q.X₁ ≫
        (tensorCoefficientTransformationAt R S B B' f hf).app Q.X₁) := by
      rw [Category.assoc, hZero]
    _ = _ := (Category.assoc _ _ _).symm

/-- For an (R,S)-bimodule B and a short exact right R-module
sequence Q, raising Γ_z to Γ′ commutes with the boundary
Tor_1(Q₃,B)→Tensor(Q₁,B).
The source comparison is the Tor height map and the target
comparison is the independent-source tensor height map. -/
theorem torBoundaryToTensorAt_height.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    (torHeightIsoAt.{t, z, r, s, a, b} R S B 1).hom.app Q.X₃ ≫
        torBoundaryToTensorAt.{max z t, r, s, a, b} R S B Q hQ =
      (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ).map
          (torBoundaryToTensorAt.{z, r, s, a, b} R S B Q hQ) ≫
        (tensorHeightFacadeIsoAt.{t, z, r, s, a, b} R S B).hom.app Q.X₁ := by
  let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
  have hDelta := torHeightIsoAt_hom_delta.{t, z, r, s, a, b} R S B 0 Q hQ
  have hZero := congrArg (fun α => α.app Q.X₁)
    (torHeightIsoAt_hom_zero.{t, z, r, s, a, b} R S B)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hZero
  unfold torBoundaryToTensorAt
  calc
    _ = (V.map (torDeltaAt.{z, r, s, a, b} R S B 0 Q hQ) ≫
        (torHeightIsoAt.{t, z, r, s, a, b} R S B 0).hom.app Q.X₁) ≫
      (torZeroIsoAt.{max z t, r, s, a, b} R S B).hom.app Q.X₁ := by
      rw [← Category.assoc, hDelta]
    _ = V.map (torDeltaAt.{z, r, s, a, b} R S B 0 Q hQ) ≫
      (V.map ((torZeroIsoAt.{z, r, s, a, b} R S B).hom.app Q.X₁) ≫
        (tensorHeightFacadeIsoAt.{t, z, r, s, a, b} R S B).hom.app Q.X₁) := by
      rw [Category.assoc, hZero]
    _ = _ := by rw [← Category.assoc, ← V.map_comp]

section CommonHeight

universe uGlobal

/-- For an (R,S)-bimodule B and a short exact right R-module
sequence Q, the windows at heights z,t become isomorphic after
both outputs are lifted to Ω=max(r,a,b,z,t,u).
All six objects and the connecting map are compared at this
same output height. -/
def torLongSequenceCommonHeightIsoAt.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ)
    (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    torLongSequenceAt.{z, r, s, a, b} R S B n Q hQ ⋙
        ModuleCat.uliftFunctor.{max r a b z t u, max r a b z} Sᵐᵒᵖ ≅
      torLongSequenceAt.{t, r, s, a, b} R S B n Q hQ ⋙
        ModuleCat.uliftFunctor.{max r a b z t u, max r a b t} Sᵐᵒᵖ :=
  torLongSequenceHeightIsoAt.{max t u, z, r, s, a, b} R S B n Q hQ ≪≫
    (torLongSequenceHeightIsoAt.{max z u, t, r, s, a, b} R S B n Q hQ).symm

/-- For an (R,S)-bimodule B and a short exact right R-module
sequence Q, the common-output comparison of the z-window with
itself is the identity.
The shared output height is Ω=max(r,a,b,z,u). -/
theorem torLongSequenceCommonHeightIsoAt_refl.{u, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (n : ℕ) (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    torLongSequenceCommonHeightIsoAt.{u, z, z, r, s, a, b} R S B n Q hQ =
      Iso.refl _ := by
  apply Iso.ext
  simp only [torLongSequenceCommonHeightIsoAt, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id, Iso.refl_hom]

/-- For an (R,S)-bimodule B and a short exact right R-module
sequence Q, the height-z to height-t window comparison has
the reversed window comparison as inverse.
Both are formed after the same common output lift. -/
theorem torLongSequenceCommonHeightIsoAt_symm.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (n : ℕ) (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    (torLongSequenceCommonHeightIsoAt.{u, t, z, r, s, a, b} R S B n Q hQ).symm =
      torLongSequenceCommonHeightIsoAt.{u, z, t, r, s, a, b} R S B n Q hQ := by
  apply Iso.ext
  simp only [torLongSequenceCommonHeightIsoAt, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv]

/-- For an (R,S)-bimodule B, a short exact right R-module
sequence Q and heights z,t,u, the z→t window comparison
followed by t→u equals z→u at Ω=max(r,a,b,z,t,u).
The identity holds on the entire five-arrow window. -/
theorem torLongSequenceCommonHeightIsoAt_trans.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (n : ℕ) (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    torLongSequenceCommonHeightIsoAt.{u, t, z, r, s, a, b} R S B n Q hQ ≪≫
        torLongSequenceCommonHeightIsoAt.{z, u, t, r, s, a, b} R S B n Q hQ =
      torLongSequenceCommonHeightIsoAt.{t, u, z, r, s, a, b} R S B n Q hQ := by
  apply Iso.ext
  simp only [torLongSequenceCommonHeightIsoAt, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]

end CommonHeight

end HeightComparison

section WindowCoefficientHeight

variable (B' : Type bGlobal) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
  [SMulCommClass R Sᵐᵒᵖ B'] (f : B →ₗ[R] B')
  (hf : ∀ (sGlobal : Sᵐᵒᵖ) (x : B), f (sGlobal • x) = sGlobal • f x)

/-- For a bimodule map f:B→B′ and a short exact right
R-module sequence Q, the window height isomorphisms commute
with the six coefficient maps.
This is a naturality square from the lifted lower-height
B-window to the higher-height B′-window. -/
theorem torLongSequenceHeightIsoAt_natural_coefficient.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (n : ℕ) (Q : ShortComplex (ModuleCat.{a} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    Functor.whiskerRight
        (torLongSequenceCoefficientMapAt.{z, r, s, a, b} R S B B' f hf n Q hQ)
        (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ) ≫
      (torLongSequenceHeightIsoAt.{t, z, r, s, a, b} R S B' n Q hQ).hom =
    (torLongSequenceHeightIsoAt.{t, z, r, s, a, b} R S B n Q hQ).hom ≫
      torLongSequenceCoefficientMapAt.{max z t, r, s, a, b} R S B B' f hf n Q hQ := by
  let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
  apply ComposableArrows.hom_ext₅
  · change V.map ((torCoefficientTransformationAt.{z, r, s, a, b}
        R S B B' f hf (n + 1)).app Q.X₁) ≫
        (torHeightIsoAt.{t, z, r, s, a, b} R S B' (n + 1)).hom.app Q.X₁ =
      (torHeightIsoAt.{t, z, r, s, a, b} R S B (n + 1)).hom.app Q.X₁ ≫
        (torCoefficientTransformationAt.{max z t, r, s, a, b}
          R S B B' f hf (n + 1)).app Q.X₁
    have h := congrArg (fun α => α.app Q.X₁)
      (torHeightIsoAt_natural_coefficient.{t, z, r, s, a, b} R S B B' f hf (n + 1))
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app] using h
  · change V.map ((torCoefficientTransformationAt.{z, r, s, a, b}
        R S B B' f hf (n + 1)).app Q.X₂) ≫
        (torHeightIsoAt.{t, z, r, s, a, b} R S B' (n + 1)).hom.app Q.X₂ =
      (torHeightIsoAt.{t, z, r, s, a, b} R S B (n + 1)).hom.app Q.X₂ ≫
        (torCoefficientTransformationAt.{max z t, r, s, a, b}
          R S B B' f hf (n + 1)).app Q.X₂
    have h := congrArg (fun α => α.app Q.X₂)
      (torHeightIsoAt_natural_coefficient.{t, z, r, s, a, b} R S B B' f hf (n + 1))
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app] using h
  · change V.map ((torCoefficientTransformationAt.{z, r, s, a, b}
        R S B B' f hf (n + 1)).app Q.X₃) ≫
        (torHeightIsoAt.{t, z, r, s, a, b} R S B' (n + 1)).hom.app Q.X₃ =
      (torHeightIsoAt.{t, z, r, s, a, b} R S B (n + 1)).hom.app Q.X₃ ≫
        (torCoefficientTransformationAt.{max z t, r, s, a, b}
          R S B B' f hf (n + 1)).app Q.X₃
    have h := congrArg (fun α => α.app Q.X₃)
      (torHeightIsoAt_natural_coefficient.{t, z, r, s, a, b} R S B B' f hf (n + 1))
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app] using h
  · change V.map ((torCoefficientTransformationAt.{z, r, s, a, b}
        R S B B' f hf (n)).app Q.X₁) ≫
        (torHeightIsoAt.{t, z, r, s, a, b} R S B' (n)).hom.app Q.X₁ =
      (torHeightIsoAt.{t, z, r, s, a, b} R S B (n)).hom.app Q.X₁ ≫
        (torCoefficientTransformationAt.{max z t, r, s, a, b}
          R S B B' f hf (n)).app Q.X₁
    have h := congrArg (fun α => α.app Q.X₁)
      (torHeightIsoAt_natural_coefficient.{t, z, r, s, a, b} R S B B' f hf (n))
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app] using h
  · change V.map ((torCoefficientTransformationAt.{z, r, s, a, b}
        R S B B' f hf (n)).app Q.X₂) ≫
        (torHeightIsoAt.{t, z, r, s, a, b} R S B' (n)).hom.app Q.X₂ =
      (torHeightIsoAt.{t, z, r, s, a, b} R S B (n)).hom.app Q.X₂ ≫
        (torCoefficientTransformationAt.{max z t, r, s, a, b}
          R S B B' f hf (n)).app Q.X₂
    have h := congrArg (fun α => α.app Q.X₂)
      (torHeightIsoAt_natural_coefficient.{t, z, r, s, a, b} R S B B' f hf (n))
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app] using h
  · change V.map ((torCoefficientTransformationAt.{z, r, s, a, b}
        R S B B' f hf (n)).app Q.X₃) ≫
        (torHeightIsoAt.{t, z, r, s, a, b} R S B' (n)).hom.app Q.X₃ =
      (torHeightIsoAt.{t, z, r, s, a, b} R S B (n)).hom.app Q.X₃ ≫
        (torCoefficientTransformationAt.{max z t, r, s, a, b}
          R S B B' f hf (n)).app Q.X₃
    have h := congrArg (fun α => α.app Q.X₃)
      (torHeightIsoAt_natural_coefficient.{t, z, r, s, a, b} R S B B' f hf (n))
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app] using h

end WindowCoefficientHeight


section SufficientOriginalWorld

universe vGlobal

local instance originalLongExactOppositeSmall (R : Type rGlobal) [Small.{vGlobal} R] :
    Small.{vGlobal} Rᵐᵒᵖ := small_of_injective MulOpposite.unop_injective

variable (C : Type vGlobal) [AddCommGroup C] [Module R C] [Module Sᵐᵒᵖ C]
  [SMulCommClass R Sᵐᵒᵖ C] [Small.{vGlobal} R]

/-- For an (R,S)-bimodule C and a short exact sequence Q
in a common carrier world v, assume R is small in v.
The comparison from unlifted Tor to height max(r,v,z)
commutes with the connecting maps in degrees n+1 and n.
No smallness premise is imposed on the outer ring S. -/
theorem torOriginalLiftIsoAt_hom_delta.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (C : Type v) [AddCommGroup C] [Module R C] [Module Sᵐᵒᵖ C]
    [SMulCommClass R Sᵐᵒᵖ C] [Small.{v} R] (n : ℕ)
    (Q : ShortComplex (ModuleCat.{v} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    (torOriginalLiftIsoAt.{z, r, s, v} R S C (n + 1)).hom.app Q.X₃ ≫
        torDeltaAt.{z, r, s, v, v} R S C n Q hQ =
      (ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ).map
        (LeftDerivedDelta.LDdelta (tensorFunctor R S C) n Q hQ) ≫
          (torOriginalLiftIsoAt.{z, r, s, v} R S C n).hom.app Q.X₁ := by
  let F := tensorFunctor R S C
  let G := largeTensorFunctorAt.{z, r, s, v, v} R S C
  let U := ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ
  let : U.PreservesHomology := Functor.preservesHomologyOfExact U
  let : V.PreservesHomology := Functor.preservesHomologyOfExact V
  let : U.PreservesProjectiveObjects := inferInstance
  exact Functor.leftDerivedTransportIso_hom_LDdelta U V F G
    (tensorOriginalLiftIsoAt.{z, r, s, v} R S C) n Q hQ


/-- For an (R,S)-bimodule C and a short exact right R-module
sequence Q in world v with R small in v, lifting the output
of its unlifted Tor window gives an isomorphism with the
window at height max(r,v,z).
Its components are the unlifted-to-sufficient Tor comparisons. -/
def torOriginalLongSequenceLiftIsoAt.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (C : Type v) [AddCommGroup C] [Module R C] [Module Sᵐᵒᵖ C]
    [SMulCommClass R Sᵐᵒᵖ C] [Small.{v} R] (n : ℕ)
    (Q : ShortComplex (ModuleCat.{v} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    LeftDerivedDelta.LDlongSequence (tensorFunctor R S C) n Q hQ ⋙
        ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ ≅
      torLongSequenceAt.{z, r, s, v, v} R S C n Q hQ := by
  let α := torOriginalLiftIsoAt.{z, r, s, v} R S C (n + 1)
  let β := torOriginalLiftIsoAt.{z, r, s, v} R S C n
  refine ComposableArrows.isoMk₅ (α.app Q.X₁) (α.app Q.X₂) (α.app Q.X₃)
    (β.app Q.X₁) (β.app Q.X₂) (β.app Q.X₃) ?_ ?_ ?_ ?_ ?_
  · exact α.hom.naturality Q.f
  · exact α.hom.naturality Q.g
  · exact (torOriginalLiftIsoAt_hom_delta R S C n Q hQ).symm
  · exact β.hom.naturality Q.f
  · exact β.hom.naturality Q.g

/-- For an (R,S)-bimodule C and a short exact sequence Q
in world v with R small in v, the degree-one Tor comparison,
the higher tensor-valued boundary and the whole-output
tensor comparison compose to the lift of the unlifted
Tor_1-to-tensor boundary. -/
theorem torOriginalBoundaryToTensorAt.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (C : Type v) [AddCommGroup C] [Module R C] [Module Sᵐᵒᵖ C]
    [SMulCommClass R Sᵐᵒᵖ C] [Small.{v} R]
    (Q : ShortComplex (ModuleCat.{v} Rᵐᵒᵖ)) (hQ : Q.ShortExact) :
    (torOriginalLiftIsoAt.{z, r, s, v} R S C 1).hom.app Q.X₃ ≫
        torBoundaryToTensorAt.{z, r, s, v, v} R S C Q hQ ≫
          (tensorOriginalLiftIsoAt.{z, r, s, v} R S C).hom.app Q.X₁ =
      (ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ).map
        (LeftDerivedDelta.LDdelta (tensorFunctor R S C) 0 Q hQ ≫
          (torZeroIso R S C).hom.app Q.X₁) := by
  let V := ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ
  have hDelta := torOriginalLiftIsoAt_hom_delta.{z, r, s, v} R S C 0 Q hQ
  have hZero := congrArg (fun α => α.app Q.X₁)
    (torOriginalLiftIsoAt_hom_zero.{z, r, s, v} R S C)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hZero
  unfold torBoundaryToTensorAt
  let α := (torOriginalLiftIsoAt.{z, r, s, v} R S C 1).hom.app Q.X₃
  let δ := torDeltaAt.{z, r, s, v, v} R S C 0 Q hQ
  let ε := (torOriginalLiftIsoAt.{z, r, s, v} R S C 0).hom.app Q.X₁
  let q := (torZeroIsoAt.{z, r, s, v, v} R S C).hom.app Q.X₁
  let e := (tensorOriginalLiftIsoAt.{z, r, s, v} R S C).hom.app Q.X₁
  let d := V.map (LeftDerivedDelta.LDdelta (tensorFunctor R S C) 0 Q hQ)
  change α ≫ (δ ≫ q) ≫ e = _
  have hΔ : α ≫ δ = d ≫ ε := hDelta
  have h₀ : (ε ≫ q) ≫ e = V.map ((torZeroIso R S C).hom.app Q.X₁) := hZero
  exact (congrArg (fun f => f ≫ e) (Category.assoc α δ q).symm).trans
    ((congrArg (fun f => (f ≫ q) ≫ e) hΔ).trans
      ((congrArg (fun f => f ≫ e) (Category.assoc d ε q)).trans
        ((Category.assoc d (ε ≫ q) e).trans
          ((congrArg (fun f => d ≫ f) h₀).trans (V.map_comp _ _).symm))))

end SufficientOriginalWorld

end ModuleCat.BalancedTensorRight
