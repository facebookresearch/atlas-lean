/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseHomologyCoherence

/-!
# Closure of TopCat local-coefficient homology equivalences

The existing map-level local-coefficient homology-equivalence predicate is
closed under identity and composition. The first equivalence can also be
cancelled from a composite. The proofs use the explicit pullback-comparison
homology maps and preserve the original coefficient systems.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe uX

namespace TopCat

/-- Identity maps are integral local-coefficient homology equivalences. -/
theorem isLocalCoefficientHomologyEquivalence_id (X : TopCat.{uX}) :
    TopCat.IsLocalCoefficientHomologyEquivalence (𝟙 X) := by
  intro L n
  rw [TopCat.localCoefficientPullbackHomologyMap_id]
  change IsIso ((SSet.localCoefficientHomologyFunctor n).map
    (Functor.whiskerLeft
      (TopCat.singularFundamentalGroupoidFunctor X)
      (TopCat.LocalSystem.pullbackIdIso L).hom))
  infer_instance

namespace IsLocalCoefficientHomologyEquivalence

/-- Composites of integral local-coefficient homology equivalences are
integral local-coefficient homology equivalences. -/
theorem comp
    {X Y Z : TopCat.{uX}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (hg : TopCat.IsLocalCoefficientHomologyEquivalence g) :
    TopCat.IsLocalCoefficientHomologyEquivalence (f ≫ g) := by
  intro L n
  rw [TopCat.localCoefficientPullbackHomologyMap_comp]
  have hCoeff : IsIso
      (SSet.localCoefficientHomologyMap
        (Functor.whiskerLeft
          (TopCat.singularFundamentalGroupoidFunctor X)
          (TopCat.LocalSystem.pullbackCompIso f g L).hom) n) := by
    change IsIso ((SSet.localCoefficientHomologyFunctor n).map
      (Functor.whiskerLeft
        (TopCat.singularFundamentalGroupoidFunctor X)
        (TopCat.LocalSystem.pullbackCompIso f g L).hom))
    infer_instance
  have hBase : IsIso
      (TopCat.localCoefficientPullbackHomologyMap
          f (L.pullback g) n ≫
        TopCat.localCoefficientPullbackHomologyMap g L n) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _
      (hf (L.pullback g) n) (hg L n)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hCoeff hBase

/-- Cancel the first local-coefficient homology equivalence from a composite.
The coefficient comparison remains the actual pullback-composition Iso. -/
public theorem of_comp
    {X Y Z : TopCat.{uX}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence f)
    (hfg : TopCat.IsLocalCoefficientHomologyEquivalence (f ≫ g)) :
    TopCat.IsLocalCoefficientHomologyEquivalence g := by
  intro L n
  let c := SSet.localCoefficientHomologyMap
    (Functor.whiskerLeft (TopCat.singularFundamentalGroupoidFunctor X)
      (TopCat.LocalSystem.pullbackCompIso f g L).hom) n
  let b := TopCat.localCoefficientPullbackHomologyMap f (L.pullback g) n
  let k := TopCat.localCoefficientPullbackHomologyMap g L n
  have hc : IsIso c := by
    change IsIso ((SSet.localCoefficientHomologyFunctor n).map
      (Functor.whiskerLeft (TopCat.singularFundamentalGroupoidFunctor X)
        (TopCat.LocalSystem.pullbackCompIso f g L).hom))
    infer_instance
  have hb : IsIso b := hf (L.pullback g) n
  let : IsIso c := hc
  let : IsIso b := hb
  have hck : IsIso ((c ≫ b) ≫ k) := by
    have he : (c ≫ b) ≫ k =
        TopCat.localCoefficientPullbackHomologyMap (f ≫ g) L n := by
      exact (Category.assoc c b k).trans
        (TopCat.localCoefficientPullbackHomologyMap_comp f g L n).symm
    rw [he]
    exact hfg L n
  let : IsIso (c ≫ b) := @IsIso.comp_isIso _ _ _ _ _ c b hc hb
  exact (isIso_comp_left_iff (c ≫ b) k).mp hck

/-- Every actual isomorphism induces an isomorphism in every degree
for every original integer local system, including nonflat systems.
The actual inverse composites and the canonical coefficient comparison
Isos suffice; no connectedness or weak-equivalence premise is needed. -/
public theorem of_isIso {X Y : TopCat.{uX}} (f : X ⟶ Y) [IsIso f] :
    TopCat.IsLocalCoefficientHomologyEquivalence f := by
  have hcomp : ∀ {S T U : TopCat.{uX}} (a : S ⟶ T) (b : T ⟶ U),
      TopCat.IsLocalCoefficientHomologyEquivalence (a ≫ b) →
        ∀ (M : TopCat.LocalSystem ℤ U) (n : ℕ),
          IsIso (TopCat.localCoefficientPullbackHomologyMap a (M.pullback b) n ≫
            TopCat.localCoefficientPullbackHomologyMap b M n) := by
    intro S T U a b hab M n
    let c := SSet.localCoefficientHomologyMap
      (Functor.whiskerLeft (TopCat.singularFundamentalGroupoidFunctor S)
        (TopCat.LocalSystem.pullbackCompIso a b M).hom) n
    have hc : IsIso c := by
      change IsIso ((SSet.localCoefficientHomologyFunctor n).map
        (Functor.whiskerLeft (TopCat.singularFundamentalGroupoidFunctor S)
          (TopCat.LocalSystem.pullbackCompIso a b M).hom))
      infer_instance
    let : IsIso c := hc
    have hm : IsIso (c ≫
        (TopCat.localCoefficientPullbackHomologyMap a (M.pullback b) n ≫
          TopCat.localCoefficientPullbackHomologyMap b M n)) := by
      have he : TopCat.localCoefficientPullbackHomologyMap (a ≫ b) M n = c ≫
          (TopCat.localCoefficientPullbackHomologyMap a (M.pullback b) n ≫
            TopCat.localCoefficientPullbackHomologyMap b M n) :=
        TopCat.localCoefficientPullbackHomologyMap_comp a b M n
      exact he ▸ hab M n
    exact (isIso_comp_left_iff c _).mp hm
  let g := inv f
  have hgf : TopCat.IsLocalCoefficientHomologyEquivalence (g ≫ f) := by
    change TopCat.IsLocalCoefficientHomologyEquivalence (inv f ≫ f)
    rw [IsIso.inv_hom_id]
    exact TopCat.isLocalCoefficientHomologyEquivalence_id Y
  have hfg : TopCat.IsLocalCoefficientHomologyEquivalence (f ≫ g) := by
    change TopCat.IsLocalCoefficientHomologyEquivalence (f ≫ inv f)
    rw [IsIso.hom_inv_id]
    exact TopCat.isLocalCoefficientHomologyEquivalence_id X
  intro L n
  let a := TopCat.localCoefficientPullbackHomologyMap f L n
  let b := TopCat.localCoefficientPullbackHomologyMap g (L.pullback f) n
  let a' := TopCat.localCoefficientPullbackHomologyMap f ((L.pullback f).pullback g) n
  have hba : IsIso (b ≫ a) := hcomp g f hgf L n
  have ha'b : IsIso (a' ≫ b) := hcomp f g hfg (L.pullback f) n
  let : IsIso (b ≫ a) := hba
  let : IsIso (a' ≫ b) := ha'b
  let : Mono b := CategoryTheory.mono_of_mono b a
  let : Epi b := CategoryTheory.epi_of_epi a' b
  let : IsIso b := CategoryTheory.isIso_of_mono_of_epi b
  exact (isIso_comp_left_iff b a).mp hba

end IsLocalCoefficientHomologyEquivalence
end TopCat
