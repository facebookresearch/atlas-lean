/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalRawComponents
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalDerivedMapping
import Mathlib.CategoryTheory.HomCongr

/-!
# Components of localized derived mapping spaces

For a working-small localizing family on a working-small, locally small site, the components
of the chosen derived mapping space identify with morphisms between the original objects in
the localized homotopy category. This equivalence respects arbitrary source and target maps
and identifies each representative using the images of the replacement counit and unit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open SimplicialPresheaf SimplicialPresheaf.InjectiveKan
open SimplicialPresheaf.OriginalLocalRawComponents SimplicialPresheaf.OriginalLocalDerived
namespace SimplicialPresheaf.OriginalLocalDerivedComponents
variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

private def imageQCounitIso (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X : (SimplicialPresheaf.{u} D)) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    (toHomotopyCategory (SimplicialPresheaf.{u} D)).obj ((localQ S).obj X) ≅
        (toHomotopyCategory (SimplicialPresheaf.{u} D)).obj X := by
  let q := originalLocalSmithData S
  letI : ModelCategory (SimplicialPresheaf.{u} D) := q.model
  apply Localization.isoOfHom (toHomotopyCategory (SimplicialPresheaf.{u} D))
      (weakEquivalences (SimplicialPresheaf.{u} D)) ((localQCounit S).app X)
  change q.model.categoryWithWeakEquivalences.weakEquivalences _
  rw [q.weakEquivalences_eq]
  exact weakEquivalences_le_originalLocalEquivalences S _
    (localQCounit_baseTrivialFibration S X).2

private def imageRUnitIso (S : I → Arrow (SimplicialPresheaf.{u} D))
    (Y : (SimplicialPresheaf.{u} D)) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    (toHomotopyCategory (SimplicialPresheaf.{u} D)).obj Y ≅
        (toHomotopyCategory (SimplicialPresheaf.{u} D)).obj ((localR S).obj Y) := by
  let q := originalLocalSmithData S
  letI : ModelCategory (SimplicialPresheaf.{u} D) := q.model
  apply Localization.isoOfHom (toHomotopyCategory (SimplicialPresheaf.{u} D))
      (weakEquivalences (SimplicialPresheaf.{u} D)) ((localRUnit S).app Y)
  change q.model.categoryWithWeakEquivalences.weakEquivalences _
  rw [q.weakEquivalences_eq]
  exact (localRUnit_localTrivialCofibration S Y).2

/-- The actual same-q derived components are morphisms in the original localized homotopy
category. -/
def localDerivedComponentHoEquiv (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X Y : (SimplicialPresheaf.{u} D)) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    SSet.π₀ (((localDerivedEnd S).obj (op X)).obj Y) ≃
      ((toHomotopyCategory (SimplicialPresheaf.{u} D)).obj X ⟶
          (toHomotopyCategory (SimplicialPresheaf.{u} D)).obj Y) := by
  letI : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
  exact (originalLocalRawMappingHoEquiv S ((localQ S).obj X) ((localR S).obj Y)
    (localR_isOriginalLocalFibrant S Y)).trans
      (Iso.homCongr (imageQCounitIso S X) (imageRUnitIso S Y).symm)

/-- Every original map QX→RY represents exactly its localized image, with BOTH actual weak unit
legs. -/
theorem localDerivedComponentHoEquiv_mk (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X Y : (SimplicialPresheaf.{u} D))
    (h : (localQ S).obj X ⟶ (localR S).obj Y) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    (toHomotopyCategory (SimplicialPresheaf.{u} D)).map ((localQCounit S).app X) ≫
      localDerivedComponentHoEquiv S X Y (SSet.π₀.mk
        (innerHomHomEquiv ((localQ S).obj X) ((localR S).obj Y) h)) ≫
      (toHomotopyCategory (SimplicialPresheaf.{u} D)).map ((localRUnit S).app Y) =
      (toHomotopyCategory (SimplicialPresheaf.{u} D)).map h := by
  let : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
  let L := toHomotopyCategory (SimplicialPresheaf.{u} D)
  let e := imageQCounitIso S X
  let r := imageRUnitIso S Y
  have hp : localDerivedComponentHoEquiv S X Y (SSet.π₀.mk
      (innerHomHomEquiv ((localQ S).obj X) ((localR S).obj Y) h)) =
      e.inv ≫ L.map h ≫ r.inv := by
    exact congrArg (fun k : L.obj ((localQ S).obj X) ⟶ L.obj ((localR S).obj Y) =>
      e.inv ≫ k ≫ r.inv)
      (originalLocalRawMappingHoEquiv_mk S ((localQ S).obj X) ((localR S).obj Y)
        (localR_isOriginalLocalFibrant S Y) h)
  have hc : e.hom ≫ (e.inv ≫ L.map h ≫ r.inv) ≫ r.hom = L.map h := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact (congrArg (fun k : L.obj X ⟶ L.obj Y => e.hom ≫ k ≫ r.hom) hp).trans hc

/-- Every original source arrow acts by its actual localized precomposition, without a weak-map
premise. -/
theorem localDerivedComponentHoEquiv_source
    (S : I → Arrow (SimplicialPresheaf.{u} D)) {A B : (SimplicialPresheaf.{u} D)}
    (f : A ⟶ B) (Y : (SimplicialPresheaf.{u} D))
        (c : SSet.π₀ (((localDerivedEnd S).obj (op B)).obj Y)) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    localDerivedComponentHoEquiv S A Y (SSet.mapπ₀ (localDerivedPrecomp S f Y) c) =
      (toHomotopyCategory (SimplicialPresheaf.{u} D)).map f ≫
          localDerivedComponentHoEquiv S B Y c := by
  let : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
  let L := toHomotopyCategory (SimplicialPresheaf.{u} D)
  obtain ⟨c,rfl⟩ := c.mk_surjective
  obtain ⟨h,rfl⟩ := (innerHomHomEquiv ((localQ S).obj B) ((localR S).obj Y)).surjective c
  let eA := imageQCounitIso S A
  let eB := imageQCounitIso S B
  let r := imageRUnitIso S Y
  let b := localDerivedComponentHoEquiv S B Y (SSet.π₀.mk
    (innerHomHomEquiv ((localQ S).obj B) ((localR S).obj Y) h))
  have hn : L.map ((localQ S).map f) ≫ eB.hom = eA.hom ≫ L.map f := by
    exact (L.map_comp ((localQ S).map f) ((localQCounit S).app B)).symm.trans
      ((L.congr_map ((localReplacement_nativeFields S).2.2 f).1).trans
        (L.map_comp ((localQCounit S).app A) f))
  have hc : SSet.mapπ₀ (innerHomPre ((localQ S).map f) ((localR S).obj Y))
      (SSet.π₀.mk (innerHomHomEquiv ((localQ S).obj B) ((localR S).obj Y) h)) =
      SSet.π₀.mk (innerHomHomEquiv ((localQ S).obj A) ((localR S).obj Y)
        ((localQ S).map f ≫ h)) :=
    (SSet.mapπ₀_mk (innerHomPre ((localQ S).map f) ((localR S).obj Y)) _).trans
      (congrArg SSet.π₀.mk (innerHomHomEquiv_precomp ((localQ S).map f) ((localR S).obj Y) h))
  have h1 : (eA.hom ≫ localDerivedComponentHoEquiv S A Y
      (SSet.mapπ₀ (innerHomPre ((localQ S).map f) ((localR S).obj Y))
        (SSet.π₀.mk (innerHomHomEquiv ((localQ S).obj B) ((localR S).obj Y) h)))) ≫ r.hom =
      (eA.hom ≫ localDerivedComponentHoEquiv S A Y
        (SSet.π₀.mk (innerHomHomEquiv ((localQ S).obj A) ((localR S).obj Y)
          ((localQ S).map f ≫ h)))) ≫ r.hom :=
    congrArg (fun x : SSet.π₀ (innerHom ((localQ S).obj A) ((localR S).obj Y)) =>
      (eA.hom ≫ localDerivedComponentHoEquiv S A Y x) ≫ r.hom) hc
  have h2 : (eA.hom ≫ localDerivedComponentHoEquiv S A Y
      (SSet.π₀.mk (innerHomHomEquiv ((localQ S).obj A) ((localR S).obj Y)
        ((localQ S).map f ≫ h)))) ≫ r.hom = L.map ((localQ S).map f ≫ h) :=
    (Category.assoc eA.hom (localDerivedComponentHoEquiv S A Y
      (SSet.π₀.mk (innerHomHomEquiv ((localQ S).obj A) ((localR S).obj Y)
        ((localQ S).map f ≫ h)))) r.hom).trans
      (localDerivedComponentHoEquiv_mk S A Y ((localQ S).map f ≫ h))
  have h3 : L.map ((localQ S).map f ≫ h) = L.map ((localQ S).map f) ≫ L.map h :=
    L.map_comp _ _
  have h4 : L.map ((localQ S).map f) ≫ L.map h =
      L.map ((localQ S).map f) ≫ (eB.hom ≫ b ≫ r.hom) :=
    congrArg (fun k : L.obj ((localQ S).obj B) ⟶ L.obj ((localR S).obj Y) =>
      L.map ((localQ S).map f) ≫ k) (localDerivedComponentHoEquiv_mk S B Y h).symm
  have h5 : L.map ((localQ S).map f) ≫ (eB.hom ≫ b ≫ r.hom) =
      (eA.hom ≫ (L.map f ≫ b)) ≫ r.hom :=
    (Category.assoc (L.map ((localQ S).map f)) eB.hom (b ≫ r.hom)).symm.trans
      ((congrArg (fun k : L.obj ((localQ S).obj A) ⟶ L.obj B => k ≫ (b ≫ r.hom)) hn).trans
        ((Category.assoc eA.hom (L.map f) (b ≫ r.hom)).trans
          ((congrArg (fun k : L.obj A ⟶ L.obj ((localR S).obj Y) => eA.hom ≫ k)
            (Category.assoc (L.map f) b r.hom).symm).trans
            (Category.assoc eA.hom (L.map f ≫ b) r.hom).symm)))
  apply (cancel_epi eA.hom).mp
  apply (cancel_mono r.hom).mp
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- Every original target arrow has the actual postcomposition action, with the SAME R unit in both
endpoints. -/
theorem localDerivedComponentHoEquiv_target (S : I → Arrow (SimplicialPresheaf.{u} D))
    (A : (SimplicialPresheaf.{u} D)) {X Y : (SimplicialPresheaf.{u} D)}
    (g : X ⟶ Y) (c : SSet.π₀ (((localDerivedEnd S).obj (op A)).obj X)) :
    letI : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
    localDerivedComponentHoEquiv S A Y (SSet.mapπ₀ (localDerivedPostcomp S A g) c) =
      localDerivedComponentHoEquiv S A X c ≫
          (toHomotopyCategory (SimplicialPresheaf.{u} D)).map g := by
  let : ModelCategory (SimplicialPresheaf.{u} D) := (originalLocalSmithData S).model
  let L := toHomotopyCategory (SimplicialPresheaf.{u} D)
  obtain ⟨c,rfl⟩ := c.mk_surjective
  obtain ⟨h,rfl⟩ := (innerHomHomEquiv ((localQ S).obj A) ((localR S).obj X)).surjective c
  let e := imageQCounitIso S A
  let rX := imageRUnitIso S X
  let rY := imageRUnitIso S Y
  let b := localDerivedComponentHoEquiv S A X (SSet.π₀.mk
    (innerHomHomEquiv ((localQ S).obj A) ((localR S).obj X) h))
  have hn : L.map g ≫ rY.hom = rX.hom ≫ L.map ((localR S).map g) := by
    exact (L.map_comp g ((localRUnit S).app Y)).symm.trans
      ((L.congr_map ((localReplacement_nativeFields S).2.2 g).2).trans
        (L.map_comp ((localRUnit S).app X) ((localR S).map g)))
  have hc : SSet.mapπ₀ (innerHomPost ((localQ S).obj A) ((localR S).map g))
      (SSet.π₀.mk (innerHomHomEquiv ((localQ S).obj A) ((localR S).obj X) h)) =
      SSet.π₀.mk (innerHomHomEquiv ((localQ S).obj A) ((localR S).obj Y)
        (h ≫ (localR S).map g)) :=
    (SSet.mapπ₀_mk (innerHomPost ((localQ S).obj A) ((localR S).map g)) _).trans
      (congrArg SSet.π₀.mk (innerHomHomEquiv_postcomp ((localQ S).obj A) ((localR S).map g) h))
  have h1 : (e.hom ≫ localDerivedComponentHoEquiv S A Y
      (SSet.mapπ₀ (innerHomPost ((localQ S).obj A) ((localR S).map g))
        (SSet.π₀.mk (innerHomHomEquiv ((localQ S).obj A) ((localR S).obj X) h)))) ≫ rY.hom =
      (e.hom ≫ localDerivedComponentHoEquiv S A Y (SSet.π₀.mk
        (innerHomHomEquiv ((localQ S).obj A) ((localR S).obj Y)
            (h ≫ (localR S).map g)))) ≫ rY.hom :=
    congrArg (fun x : SSet.π₀ (innerHom ((localQ S).obj A) ((localR S).obj Y)) =>
      (e.hom ≫ localDerivedComponentHoEquiv S A Y x) ≫ rY.hom) hc
  have h2 : (e.hom ≫ localDerivedComponentHoEquiv S A Y (SSet.π₀.mk
      (innerHomHomEquiv ((localQ S).obj A) ((localR S).obj Y) (h ≫ (localR S).map g)))) ≫ rY.hom =
      L.map (h ≫ (localR S).map g) :=
    (Category.assoc e.hom (localDerivedComponentHoEquiv S A Y (SSet.π₀.mk
      (innerHomHomEquiv ((localQ S).obj A) ((localR S).obj Y) (h ≫ (localR S).map g))))
          rY.hom).trans
      (localDerivedComponentHoEquiv_mk S A Y (h ≫ (localR S).map g))
  have h3 : L.map (h ≫ (localR S).map g) = L.map h ≫ L.map ((localR S).map g) := L.map_comp _ _
  have h4 : L.map h ≫ L.map ((localR S).map g) =
      (e.hom ≫ b ≫ rX.hom) ≫ L.map ((localR S).map g) :=
    congrArg (fun k : L.obj ((localQ S).obj A) ⟶ L.obj ((localR S).obj X) =>
      k ≫ L.map ((localR S).map g)) (localDerivedComponentHoEquiv_mk S A X h).symm
  have h5 : (e.hom ≫ b ≫ rX.hom) ≫ L.map ((localR S).map g) =
      (e.hom ≫ (b ≫ L.map g)) ≫ rY.hom :=
    (Category.assoc e.hom (b ≫ rX.hom) (L.map ((localR S).map g))).trans
      ((congrArg (fun k : L.obj A ⟶ L.obj ((localR S).obj Y) => e.hom ≫ k)
        (Category.assoc b rX.hom (L.map ((localR S).map g)))).trans
        ((congrArg (fun k : L.obj X ⟶ L.obj ((localR S).obj Y) => e.hom ≫ (b ≫ k)) hn.symm).trans
          ((congrArg (fun k : L.obj A ⟶ L.obj ((localR S).obj Y) => e.hom ≫ k)
            (Category.assoc b (L.map g) rY.hom).symm).trans
            (Category.assoc e.hom (b ≫ L.map g) rY.hom).symm)))
  apply (cancel_epi e.hom).mp
  apply (cancel_mono rY.hom).mp
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

end SimplicialPresheaf.OriginalLocalDerivedComponents
