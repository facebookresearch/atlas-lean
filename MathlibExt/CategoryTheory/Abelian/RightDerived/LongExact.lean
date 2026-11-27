/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Author: @toskua, Avocado

Copyright (c) 2026 @junekim623, Muse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @junekim623, Muse

-/
module

public import MathlibExt.CategoryTheory.Iso
public import MathlibExt.Algebra.Homology.ShortComplex.Exact
public import MathlibExt.CategoryTheory.Abelian.Injective.Horseshoe
public import MathlibExt.CategoryTheory.Abelian.RightDerived.Additive
public import MathlibExt.CategoryTheory.Abelian.RightDerived.HorseshoeData
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ResolutionComparison
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Right-derived long exact sequences from endpoint resolutions

Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. For short exact `X₁ → X₂ → X₃`, prescribed
injective resolutions of `X₁,X₃` give a degreewise split horseshoe.
Its mapped cohomology boundary, transported through the resolution
comparisons, is `R^nF(X₃) → R^(n+1)F(X₁)`. The resulting five-arrow
window is exact at each interior term. Coefficient transformation
squares transport from mapped resolution cohomology to derived objects.
-/

@[expose] public section

namespace CategoryTheory
open Category Limits
open scoped ZeroObject

universe v₁ u₁ v₂ u₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

namespace NatTrans

/-- Let `A,B` be categories with zero morphisms, `c` any complex
shape, and `F,G,H,L : A → B` preserve zero morphisms. If natural
transformations satisfy `α ≫ β = γ ≫ δ`, their induced maps on
any `c`-shaped complex `K` satisfy the same commuting square. -/
lemma mapHomologicalComplex_app_comp_eq
    {A B : Type*} [Category A] [Category B] [HasZeroMorphisms A] [HasZeroMorphisms B]
    {ι : Type*} (c : ComplexShape ι) {F G H L : A ⥤ B}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [H.PreservesZeroMorphisms] [L.PreservesZeroMorphisms]
    (α : F ⟶ G) (β : G ⟶ H) (γ : F ⟶ L) (δ : L ⟶ H)
    (h : α ≫ β = γ ≫ δ) (K : HomologicalComplex A c) :
    (NatTrans.mapHomologicalComplex α c).app K ≫
        (NatTrans.mapHomologicalComplex β c).app K =
      (NatTrans.mapHomologicalComplex γ c).app K ≫
        (NatTrans.mapHomologicalComplex δ c).app K := by
  rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
    ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, h]

/-- Let `A,B` be categories with zero morphisms, `c` any complex
shape, and `F,G,H : A → B` preserve zero morphisms. If natural
transformations `α : F → G`, `β : G → H` have zero composite,
their induced maps on any `c`-shaped complex have zero composite. -/
lemma mapHomologicalComplex_app_comp_eq_zero
    {A B : Type*} [Category A] [Category B] [HasZeroMorphisms A] [HasZeroMorphisms B]
    {ι : Type*} (c : ComplexShape ι) {F G H : A ⥤ B}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (α : F ⟶ G) (β : G ⟶ H) (h : α ≫ β = 0) (K : HomologicalComplex A c) :
    (NatTrans.mapHomologicalComplex α c).app K ≫
        (NatTrans.mapHomologicalComplex β c).app K = 0 := by
  rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, h]
  apply HomologicalComplex.Hom.ext
  funext i
  rfl

end NatTrans

namespace InjectiveResolution

set_option backward.isDefEq.respectTransparency false in
/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`R` an injective resolution of `X`. For additive `F₁,F₂,G₁,G₂ : C → D`,
transformations `α : F₂ → F₁`, `β : G₂ → G₁`, and maps
`d_k : Hⁿ(F_k(R)) → Hᵐ(G_k(R))`, suppose
`d₂ ≫ Hᵐ(β_R) = Hⁿ(α_R) ≫ d₁`. Transporting by the resolution
comparisons gives the corresponding square with `R^nα_X` and `R^mβ_X`. -/
lemma conjugateHomology_naturality
    {F₁ F₂ G₁ G₂ : C ⥤ D} [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    {X : C} (R : InjectiveResolution X) (α : F₂ ⟶ F₁) (β : G₂ ⟶ G₁) (n m : ℕ)
    (d₁ : ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex).homology n ⟶
      ((G₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex).homology m)
    (d₂ : ((F₂.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex).homology n ⟶
      ((G₂.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex).homology m)
    (h : d₂ ≫ HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℕ)).app R.cocomplex) m =
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app R.cocomplex) n ≫ d₁) :
    ((R.isoRightDerivedObj F₂ n).hom ≫ d₂ ≫ (R.isoRightDerivedObj G₂ m).inv) ≫
        (NatTrans.rightDerived β m).app X =
      (NatTrans.rightDerived α n).app X ≫
        ((R.isoRightDerivedObj F₁ n).hom ≫ d₁ ≫ (R.isoRightDerivedObj G₁ m).inv) := by
  exact Iso.conjugate_naturality
    (R.isoRightDerivedObj F₁ n) (R.isoRightDerivedObj F₂ n)
    (R.isoRightDerivedObj G₁ m) (R.isoRightDerivedObj G₂ m) d₁ d₂
    ((NatTrans.rightDerived α n).app X) ((NatTrans.rightDerived β m).app X)
    (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app R.cocomplex) n)
    (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex β (ComplexShape.up ℕ)).app R.cocomplex) m)
    (R.isoRightDerivedObj_hom_naturality_functor α n)
    (R.isoRightDerivedObj_inv_naturality_functor β m) h

end InjectiveResolution

namespace RightDerivedDelta

/-- Let `C,D` be abelian, `F : C → D` additive, `S : X₁ → X₂ → X₃`
short exact, and `I₁,I₃` injective resolutions of its endpoints. The endpoint injective horseshoe mapped by `F` is the short
complex of nonnegative cochain complexes
`F(I₁) → F(I₂) → F(I₃)`, with `I₂` the horseshoe middle resolution. -/
noncomputable def RDhorseshoeF (F : C ⥤ D) [F.Additive] (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) : ShortComplex (CochainComplex D ℕ)  :=
  (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).mapped F

omit [HasInjectiveResolutions C] in
/-- Let `C,D` be abelian, `F : C → D` additive, `S : X₁ → X₂ → X₃`
short exact, and `I₁,I₃` injective resolutions of its endpoints. The mapped endpoint horseshoe is a short exact sequence of
cochain complexes, since its degreewise biproduct splittings remain
splittings under `F`. -/
theorem RDhorseshoeF_shortExact (F : C ⥤ D) [F.Additive] (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    (RDhorseshoeF F S hS I₁ I₃).ShortExact  :=
  (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).mapped_shortExact F

/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive, `S : X₁ → X₂ → X₃` short exact, and
`I₁,I₃` injective resolutions of its endpoints. The transported cohomology boundary of the endpoint horseshoe
defines `δ_n : R^nF(X₃) → R^(n+1)F(X₁)`. -/
noncomputable def RDdelta (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    (F.rightDerived n).obj S.X₃ ⟶ (F.rightDerived (n + 1)).obj S.X₁  :=
  (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).delta F n (n + 1) rfl

/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive, `S : X₁ → X₂ → X₃` short exact, and
`I₁,I₃` injective resolutions of its endpoints. For any short-exactness witness on the mapped horseshoe,
`δ_n` is the comparison to `Hⁿ(F(I₃))`, followed by its cohomology
boundary and the inverse comparison from `H^(n+1)(F(I₁))`. -/
theorem RDdelta_eq (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃)
    (hHF : (RDhorseshoeF F S hS I₁ I₃).ShortExact) :
    RDdelta F n S hS I₁ I₃ =
      (I₃.isoRightDerivedObj F n).hom ≫
        hHF.δ n (n + 1) (ComplexShape.up_mk _ _ rfl) ≫
        (I₁.isoRightDerivedObj F (n + 1)).inv := rfl

omit [HasInjectiveResolutions C] in
/-- Let `C,D` be abelian, `F : C → D` additive, `S : X₁ → X₂ → X₃`
short exact, and `I₁,I₃` injective resolutions of its endpoints. Its mapped endpoint-horseshoe diagram is the diagram obtained
by applying `F` to the compatible horseshoe data constructed from
`I₁,I₃`. -/
lemma RDhorseshoeF_eq_mapped (F : C ⥤ D) [F.Additive] (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    RDhorseshoeF F S hS I₁ I₃ =
      (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).mapped F := rfl

/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive, `S : X₁ → X₂ → X₃` short exact, and
`I₁,I₃` injective resolutions of its endpoints. The endpoint boundary `δ_n` equals the connecting map of
the compatible horseshoe data constructed from `I₁,I₃`. -/
lemma RDdelta_eq_ofEndpoints (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    RDdelta F n S hS I₁ I₃ =
      (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).delta
        F n (n + 1) rfl := rfl

/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive, `S : X₁ → X₂ → X₃` short exact, and
`I₁,I₃` injective resolutions of its endpoints. The five-arrow window from the compatible endpoint data has
maps `R^nF(S.f)`, `R^nF(S.g)`, `δ_n`, `R^(n+1)F(S.f)`,
and `R^(n+1)F(S.g)` in that order. -/
lemma RDlongSequence_eq (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).longSequence
        F n (n + 1) rfl =
      ComposableArrows.mk₅ ((F.rightDerived n).map S.f) ((F.rightDerived n).map S.g)
        (RDdelta F n S hS I₁ I₃) ((F.rightDerived (n + 1)).map S.f)
        ((F.rightDerived (n + 1)).map S.g) := rfl

omit [HasInjectiveResolutions C] in
/-- Let `C,D` be abelian, `F : C → D` additive, `S : X₁ → X₂ → X₃`
short exact, and `I₁,I₃` injective resolutions of its endpoints. In each degree `n`, the cohomology map of the mapped left
horseshoe inclusion followed by that of its right projection is zero. -/
theorem RDles_middle_zero (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex _).map
          (InjectiveResolution.horseshoe (hS := hS) (I₁ := I₁)
            (I₃ := I₃)).i) n ≫
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex _).map
          (InjectiveResolution.horseshoe (hS := hS) (I₁ := I₁)
            (I₃ := I₃)).p) n = 0 := by
  rw [← HomologicalComplex.homologyMap_comp,
    ← (F.mapHomologicalComplex _).map_comp,
    (InjectiveResolution.horseshoe (hS := hS) (I₁ := I₁)
      (I₃ := I₃)).zero]
  simp

/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive, `S : X₁ → X₂ → X₃` short exact, and
`I₁,I₃` injective resolutions of its endpoints. The sequence
`R^nF(X₃) → R^(n+1)F(X₁) → R^(n+1)F(X₂)` has zero composite
and is exact at `R^(n+1)F(X₁)`. -/
theorem RDexact_A (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    ∃ w : RDdelta F n S hS I₁ I₃ ≫ (F.rightDerived (n + 1)).map S.f = 0,
      (ShortComplex.mk _ _ w).Exact  := by
  have h := (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).longSequence_exact
    F n (n + 1) rfl
  exact ⟨h.toIsComplex.zero 2, h.exact 2⟩

/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive, `S : X₁ → X₂ → X₃` short exact, and
`I₁,I₃` injective resolutions of its endpoints. The sequence `R^nF(X₁) → R^nF(X₂) → R^nF(X₃)` has zero
composite and is exact at `R^nF(X₂)`. -/
theorem RDexact_B (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    ∃ w : (F.rightDerived n).map S.f ≫ (F.rightDerived n).map S.g = 0,
      (ShortComplex.mk _ _ w).Exact  := by
  have h := (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).longSequence_exact
    F n (n + 1) rfl
  exact ⟨h.toIsComplex.zero 0, h.exact 0⟩

/-- Let `C,D` be abelian, with injective resolutions in `C`,
`F : C → D` additive, `S : X₁ → X₂ → X₃` short exact, and
`I₁,I₃` injective resolutions of its endpoints. The sequence `R^nF(X₂) → R^nF(X₃) → R^(n+1)F(X₁)` has
zero composite and is exact at `R^nF(X₃)`. -/
theorem RDexact_C (F : C ⥤ D) [F.Additive] (n : ℕ) (S : ShortComplex C)
    (hS : S.ShortExact) (I₁ : InjectiveResolution S.X₁)
    (I₃ : InjectiveResolution S.X₃) :
    ∃ w : (F.rightDerived n).map S.g ≫ RDdelta F n S hS I₁ I₃ = 0,
      (ShortComplex.mk _ _ w).Exact  := by
  have h := (Functor.RightDerived.HorseshoeData.ofEndpoints S hS I₁ I₃).longSequence_exact
    F n (n + 1) rfl
  exact ⟨h.toIsComplex.zero 1, h.exact 1⟩

end RightDerivedDelta

end CategoryTheory
