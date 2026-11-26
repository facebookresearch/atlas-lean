/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.PrecompositionCoherence

-- Authors: @toskua, Avocado

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory

namespace CategoryTheory.CohomologicalDeltaFunctor
variable {A B D : Type*} [Category A] [Preadditive A]
variable [Category B] [Preadditive B] [Category D] [Preadditive D]

/-- Let `A`, `B`, `D` be preadditive categories, `R,R′ : A → B`
additive functors preserving short exact sequences, and `e : R ≅ R′`.
For a cohomological δ-functor `T : B → D`, the two precomposed
δ-functors along `R` and `R′` are isomorphic, through the comparisons
induced by `e` in every degree. -/
def precomposeChangeIso (R R' : A ⥤ B) [R.Additive] [R'.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (hR' : ∀ S : ShortComplex A, S.ShortExact → (S.map R').ShortExact)
    (e : R ≅ R') (T : CohomologicalDeltaFunctor B D) :
    precompose R hR T ≅ precompose R' hR' T where
  hom := precomposeChangeHom R R' hR hR' e.hom T
  inv := precomposeChangeHom R' R hR' hR e.inv T
  hom_inv_id := by
    apply hom_ext
    intro q
    ext M
    change (T.T q).map (e.hom.app M) ≫ (T.T q).map (e.inv.app M) = 𝟙 _
    rw [← Functor.map_comp, e.hom_inv_id_app, Functor.map_id]
  inv_hom_id := by
    apply hom_ext
    intro q
    ext M
    change (T.T q).map (e.inv.app M) ≫ (T.T q).map (e.hom.app M) = 𝟙 _
    rw [← Functor.map_comp, e.inv_hom_id_app, Functor.map_id]

theorem precomposeChangeIso_hom_app (R R' : A ⥤ B) [R.Additive] [R'.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (hR' : ∀ S : ShortComplex A, S.ShortExact → (S.map R').ShortExact)
    (e : R ≅ R') (T : CohomologicalDeltaFunctor B D) (q : ℕ) :
    Hom.app (precomposeChangeIso R R' hR hR' e T).hom q =
      Functor.whiskerRight e.hom (T.T q) := rfl

end CategoryTheory.CohomologicalDeltaFunctor

end

section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory.CohomologicalDeltaFunctor
variable {A D : Type*} [Category A] [Preadditive A] [Category D] [Preadditive D]

/-- For cohomological δ-functors `S,T : A → D` between preadditive
categories, suppose an isomorphism `e : S ≅ T` has degree components
the chosen natural isomorphisms `c_q`. For a short exact sequence
`Z : X₁ → X₂ → X₃`, their connecting maps satisfy
`δ_S,q ≫ c_(q+1)(X₁) = c_q(X₃) ≫ δ_T,q`. -/
theorem iso_connecting_eq_components {S T : CohomologicalDeltaFunctor A D}
    (e : S ≅ T) (c : ∀ q, S.T q ≅ T.T q)
    (hc : ∀ q, Hom.app e.hom q = (c q).hom)
    (q : ℕ) (Z : ShortComplex.ShortExactSequences A) :
    (S.connecting q).app Z ≫ (c (q + 1)).hom.app Z.obj.X₁ =
      (c q).hom.app Z.obj.X₃ ≫ (T.connecting q).app Z := by
  have h := DeltaFunctor.System.comm e.hom.hom q Z
  change (S.connecting q).app Z ≫ (Hom.app e.hom (q + 1)).app Z.obj.X₁ =
    (Hom.app e.hom q).app Z.obj.X₃ ≫ (T.connecting q).app Z at h
  rw [hc (q + 1), hc q] at h
  exact h

end CategoryTheory.CohomologicalDeltaFunctor

end
