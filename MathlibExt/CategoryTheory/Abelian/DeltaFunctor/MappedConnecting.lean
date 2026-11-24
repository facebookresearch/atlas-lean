/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Precomposition
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.PrecompositionCoherence

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u v u' v' u'' v'' uD vD
namespace CategoryTheory.CohomologicalDeltaFunctor
variable {A : Type u} [Category.{v} A] [Preadditive A]
variable {B : Type u'} [Category.{v'} B] [Preadditive B]
variable {C : Type u''} [Category.{v''} C] [Preadditive C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]

/-- The precomposed connector, with its ordinary mapped-object endpoints. -/
def mappedConnecting (R : A ⥤ B) [R.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (T : CohomologicalDeltaFunctor B D) (q : ℕ)
    (S : ShortComplex A) (hS : S.ShortExact) :
    (T.T q).obj (R.obj S.X₃) ⟶ (T.T (q + 1)).obj (R.obj S.X₁) :=
  (T.connecting q).app ⟨S.map R, hR S hS⟩

/--
Delta-isomorphism components commute with these same ordinary endpoint arrows. The mapped exact
sequences are constructed by hR and hF.
-/
theorem mappedConnecting_iso_components
    (R : A ⥤ B) [R.Additive] (F : A ⥤ C) [F.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (hF : ∀ S : ShortComplex A, S.ShortExact → (S.map F).ShortExact)
    (T : CohomologicalDeltaFunctor B D) (U : CohomologicalDeltaFunctor C D)
    (e : precompose R hR T ≅ precompose F hF U)
    (c : ∀ q, R ⋙ T.T q ≅ F ⋙ U.T q)
    (hc : ∀ q, Hom.app e.hom q = (c q).hom)
    (q : ℕ) (S : ShortComplex A) (hS : S.ShortExact) :
    mappedConnecting R hR T q S hS ≫ (c (q + 1)).hom.app S.X₁ =
      (c q).hom.app S.X₃ ≫ mappedConnecting F hF U q S hS := by
  have h := DeltaFunctor.System.comm e.hom.hom q ⟨S, hS⟩
  change ((precompose R hR T).connecting q).app ⟨S, hS⟩ ≫
      (Hom.app e.hom (q + 1)).app S.X₁ =
    (Hom.app e.hom q).app S.X₃ ≫ ((precompose F hF U).connecting q).app ⟨S, hS⟩ at h
  rw [hc (q + 1), hc q] at h
  exact h

end CategoryTheory.CohomologicalDeltaFunctor

end
