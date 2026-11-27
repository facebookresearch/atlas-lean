/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGenerators
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornCoproductPushoutWeakHomotopy

/-!
# Weak homotopy equivalences from horn coproduct pushouts

A family of maps in the realized-horn generator class admits a pointwise
presentation by standard realized horn inclusions. A pushout whose top arrow
is isomorphic to a categorical coproduct of positive-dimensional realized horns
has a weak homotopy-equivalence opposite leg.

Consequently every pushout of an arbitrary coproduct presentation of realized
horn inclusions is a weak homotopy equivalence.
-/

@[expose] public section

universe u

open CategoryTheory

namespace TopCat

/--
For a family of realized horn inclusions, there exist dimensions and horn indices
identifying each family arrow with a standard realized horn inclusion.
-/
theorem hornFamily_arrow_eq {J : Type u} {A B : J → TopCat.{u}}
    {m : ∀ j, A j ⟶ B j} (hm : ∀ j, realizedHornInclusions.{u} (m j)) :
    ∃ (N : J → ℕ) (K : ∀ j, Fin (N j + 1)),
      ∀ j, Arrow.mk (m j) =
        Arrow.mk (SSet.toTop.map (SSet.horn.{u} (N j) (K j)).ι) := by
  simp only [realizedHornInclusions, MorphismProperty.iSup_iff,
    MorphismProperty.ofHoms_iff] at hm
  choose N I hArrow using hm
  exact ⟨fun j => N j + 1, fun j => I j, fun j => hArrow j⟩

/--
For a positive-dimensional horn family, if the top arrow of a pushout is
isomorphic to its categorical coproduct inclusion, the opposite pushout leg is
a weak homotopy equivalence.
-/
theorem hornCoproduct_pushout_of_arrow_iso
    {J : Type u} {N : J → ℕ} {K : ∀ j, Fin (N j + 1)} {hn : ∀ j, 0 < N j}
    {A B X Y : TopCat.{u}} {p : A ⟶ B} {f : A ⟶ X} {g : B ⟶ Y}
    {q : X ⟶ Y}
    (e : Arrow.mk p ≅
      Arrow.mk (Limits.Sigma.map (fun j => hornSDRIncl J N K j)))
    (h : IsPushout p f g q) :
    weakHomotopyEquivalences q := by
  let eL : A ≅ _ := Arrow.leftFunc.mapIso e
  let eR : B ≅ _ := Arrow.rightFunc.mapIso e
  have commf : p ≫ eR.hom =
      eL.hom ≫ Limits.Sigma.map (fun j => hornSDRIncl J N K j) :=
    (e.hom.w).symm
  have commg : f ≫ (Iso.refl X).hom = eL.hom ≫ (eL.inv ≫ f) := by
    simp
  have comminl : g ≫ (Iso.refl Y).hom = eR.hom ≫ (eR.inv ≫ g) := by
    simp
  have comminr : q ≫ (Iso.refl Y).hom = (Iso.refl X).hom ≫ q := by simp
  have h' : IsPushout (Limits.Sigma.map (fun j => hornSDRIncl J N K j))
      (eL.inv ≫ f) (eR.inv ≫ g) q :=
    h.of_iso eL eR (Iso.refl X) (Iso.refl Y)
      commf commg comminl comminr
  exact hornCoproduct_pushout_inr_mem_weakHomotopyEquivalences
    (J := J) (n := N) (k := K) (hn := hn) h'

/--
Every pushout of a coproduct of realized horn inclusions is a weak homotopy
equivalence.
-/
theorem coproducts_pushouts_le_weakHomotopyEquivalences :
    (MorphismProperty.coproducts.{u} TopCat.realizedHornInclusions.{u}).pushouts ≤
      TopCat.weakHomotopyEquivalences.{u} := by
  intro X Y q hq
  obtain ⟨A, B, p, f, g, hp, h⟩ := hq
  rw [MorphismProperty.coproducts_iff] at hp
  obtain ⟨J, hcol⟩ := hp
  obtain ⟨X₁, X₂, c₁, c₂, h₁, h₂, fNat, hf⟩ := hcol
  have hm : ∀ j : J,
      TopCat.realizedHornInclusions (fNat.app (Discrete.mk j)) :=
    fun j => hf (Discrete.mk j)
  simp only [TopCat.realizedHornInclusions, MorphismProperty.iSup_iff,
    MorphismProperty.ofHoms_iff] at hm
  choose n₀ I hArrow₀ using hm
  let φm := fun j : J => fNat.app (Discrete.mk j)
  let φh := fun j : J =>
    TopCat.hornSDRIncl J (fun i => n₀ i + 1) (fun i => I i) j
  have hA : ∀ j : J, Arrow.mk (φm j) = Arrow.mk (φh j) := hArrow₀
  have hn : ∀ j : J, 0 < n₀ j + 1 := fun j => Nat.succ_pos _
  have eColim : Arrow.mk (Limits.Sigma.map φm) ≅
      Arrow.mk (h₁.desc (Limits.Cocone.mk _ (fNat ≫ c₂.ι))) :=
    Arrow.isoMk
      ((Limits.Sigma.isoColimit X₁) ≪≫
        Limits.IsColimit.coconePointUniqueUpToIso
          (Limits.colimit.isColimit X₁) h₁)
      ((Limits.Sigma.isoColimit X₂) ≪≫
        Limits.IsColimit.coconePointUniqueUpToIso
          (Limits.colimit.isColimit X₂) h₂) (by
      apply Limits.colimit.hom_ext
      rintro ⟨j⟩
      simp [φm])
  let eL : ∀ j : J, X₁.obj (Discrete.mk j) ≅
      TopCat.hornSDRDomain J (fun i => n₀ i + 1) (fun i => I i) j :=
    fun j => Arrow.leftFunc.mapIso (eqToIso (hA j))
  let eR : ∀ j : J, X₂.obj (Discrete.mk j) ≅
      TopCat.hornSDRSimplex J (fun i => n₀ i + 1) j :=
    fun j => Arrow.rightFunc.mapIso (eqToIso (hA j))
  have wj : ∀ j : J, (eL j).hom ≫ φh j = φm j ≫ (eR j).hom :=
    fun j => (eqToIso (hA j)).hom.w
  have hcomm_pw : (Limits.Sigma.mapIso eL).hom ≫ Limits.Sigma.map φh =
      Limits.Sigma.map φm ≫ (Limits.Sigma.mapIso eR).hom := by
    apply Limits.Sigma.hom_ext
    intro j
    calc Limits.Sigma.ι _ j ≫ ((Limits.Sigma.mapIso eL).hom ≫ Limits.Sigma.map φh)
        = ((eL j).hom ≫ φh j) ≫ Limits.Sigma.ι _ j := by
          rw [← Category.assoc, Limits.Sigma.ι_mapIso_hom, Category.assoc,
            Limits.Sigma.ι_map, ← Category.assoc]
      _ = ((φm j ≫ (eR j).hom)) ≫ Limits.Sigma.ι _ j := by
          rw [wj j]
      _ = Limits.Sigma.ι _ j ≫ (Limits.Sigma.map φm ≫
            (Limits.Sigma.mapIso eR).hom) := by
          have step3 : Limits.Sigma.ι _ j ≫ (Limits.Sigma.map φm ≫
              (Limits.Sigma.mapIso eR).hom) =
              ((φm j ≫ (eR j).hom)) ≫ Limits.Sigma.ι _ j := by
            rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc,
              Limits.Sigma.ι_mapIso_hom, ← Category.assoc]
          exact step3.symm
  have ePw : Arrow.mk (Limits.Sigma.map φm) ≅
      Arrow.mk (Limits.Sigma.map φh) :=
    Arrow.isoMk (Limits.Sigma.mapIso eL) (Limits.Sigma.mapIso eR) hcomm_pw
  have e : Arrow.mk (h₁.desc (Limits.Cocone.mk _ (fNat ≫ c₂.ι))) ≅
      Arrow.mk (Limits.Sigma.map φh) :=
    eColim.symm ≪≫ ePw
  exact TopCat.hornCoproduct_pushout_of_arrow_iso (hn := hn) e h.flip

end TopCat
