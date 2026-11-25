/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.OrderedAffineCover.IterCechCup

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- The source statement, with its original binders. -/
set_option linter.unusedVariables false in
example
    {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k))
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover)
    (haff : ∀ i j, IsAffineOpen ((𝔘.preimageFamily (pullback.fst πX πY)).U i ⊓
      (𝔙.preimageFamily (pullback.snd πX πY)).U j))
    (hcov : ⨆ ij : 𝔘.ι × 𝔙.ι,
      (𝔘.preimageFamily (pullback.fst πX πY)).U ij.1 ⊓
        (𝔙.preimageFamily (pullback.snd πX πY)).U ij.2 = ⊤)
    (i : DoubleComplex.Diag 0)
    (α : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝔘 i.1.1)))
    (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝔙 i.1.2))) :
    (OModulePresheaf.IterCech.augTot (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover
              (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).toOpenFamily
            0
            (Pi.single i
              (fun st : 𝔘.Idx i.1.1 × 𝔙.Idx i.1.2 =>
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_left.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.fst πX πY)
                      (fun j => 𝔘.U (st.1.1 j))).symm))).op).hom
                  (((pullback.fst πX πY).app (𝔘.inter st.1)).hom (α.1 st.1)) *
                ((pullback πX πY).presheaf.map (homOfLE (inf_le_right.trans
                    (le_of_eq (Scheme.OrderedAffineCover.preimage_iInf_fin (pullback.snd πX πY)
                      (fun j => 𝔙.U (st.2.1 j))).symm))).op).hom
                  (((pullback.snd πX πY).app (𝔙.inter st.2)).hom (β.1 st.2)) :
                OModulePresheaf.BiCech.C (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
                  (𝔘.preimageFamily (pullback.fst πX πY))
                  (𝔙.preimageFamily (pullback.snd πX πY)) i.1.1 i.1.2) :
              DoubleComplex.Tot ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).biCech
                (𝔘.preimageFamily (pullback.fst πX πY))
                (𝔙.preimageFamily (pullback.snd πX πY))) 0))
      = (OModulePresheaf.IterCech.augCech (OModulePresheaf.unit (pullback.fst πX πY ≫ πX))
            (𝔘.preimageFamily (pullback.fst πX πY)) (𝔙.preimageFamily (pullback.snd πX πY))
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover
              (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
            0
            ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup
              ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover
                (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
              i.1.1 i.1.2 0 i.2
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover
                  (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔘
                (fun ij => (ofLex ij).1) (fun ij => inf_le_left) i.1.1 α.1)
              (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY)
                ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover
                  (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔙
                (fun ij => (ofLex ij).2) (fun ij => inf_le_right) i.1.2 β.1))) :=
  OModulePresheaf.IterCech.augTot_single_eq_augCech_cup_zero πX πY 𝔘 𝔙 haff hcov i α β

/- The product cover is indexed by the lexicographic product of the two index types. -/
example {Z : Scheme.{u}} (𝔄 𝔅 : Z.OrderedOpenFamily)
    (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j))
    (hcov : ⨆ ij : 𝔄.ι × 𝔅.ι, 𝔄.U ij.1 ⊓ 𝔅.U ij.2 = ⊤) :
    (𝔄.prodCover 𝔅 haff hcov).ι = (𝔄.ι ×ₗ 𝔅.ι) :=
  rfl

/-! ### A concrete instance: `Spec ℤ ×_ℤ Spec ℤ` with one-open covers -/

/-- The cover of `Spec ℤ` by the single open `⊤`. -/
private noncomputable def topCover : (Spec (CommRingCat.of ℤ)).OrderedAffineCover where
  ι := Fin 1
  U _ := ⊤
  isAffineOpen _ := isAffineOpen_top _
  iSup_eq_top := iSup_const

/-- `𝟙 (Spec ℤ)`, the structure morphism of `Spec ℤ` over itself. -/
private noncomputable abbrev πℤ : Spec (CommRingCat.of ℤ) ⟶ Spec (CommRingCat.of ℤ) := 𝟙 _

private theorem haff_topCover : ∀ i j,
    IsAffineOpen ((topCover.preimageFamily (pullback.fst πℤ πℤ)).U i ⊓
      (topCover.preimageFamily (pullback.snd πℤ πℤ)).U j) := fun _ _ => by
  change IsAffineOpen (pullback.fst πℤ πℤ ⁻¹ᵁ ⊤ ⊓ pullback.snd πℤ πℤ ⁻¹ᵁ ⊤)
  rw [Scheme.Hom.preimage_top, Scheme.Hom.preimage_top, inf_top_eq]
  exact isAffineOpen_top _

private theorem hcov_topCover : ⨆ ij : topCover.ι × topCover.ι,
    (topCover.preimageFamily (pullback.fst πℤ πℤ)).U ij.1 ⊓
      (topCover.preimageFamily (pullback.snd πℤ πℤ)).U ij.2 = ⊤ := by
  change ⨆ _ij : Fin 1 × Fin 1, pullback.fst πℤ πℤ ⁻¹ᵁ ⊤ ⊓ pullback.snd πℤ πℤ ⁻¹ᵁ ⊤ = ⊤
  rw [Scheme.Hom.preimage_top, Scheme.Hom.preimage_top, inf_top_eq, iSup_const]

/-- A one-open cover has no strictly increasing pairs of indices. -/
private theorem isEmpty_topCover_idx_one : IsEmpty (topCover.Idx 1) := by
  refine ⟨fun s => ?_⟩
  have hlt := s.2 (show (0 : Fin 2) < 1 by decide)
  rw [Subsingleton.elim (α := Fin 1) (s.1 1) (s.1 0)] at hlt
  exact lt_irrefl _ hlt

/-- On a one-open cover every degree-zero cochain is a cocycle. -/
private theorem d_topCover_eq_zero (α : (OModulePresheaf.unit πℤ).cochain topCover 0) :
    (OModulePresheaf.unit πℤ).d topCover 0 α = 0 :=
  funext fun s => (isEmpty_topCover_idx_one.false s).elim

/-- The hypotheses `haff` and `hcov` hold for the one-open covers of `Spec ℤ`, so the theorem
applies to any pair of degree-zero cochains there. -/
example (α β : (OModulePresheaf.unit πℤ).cochain topCover 0) :=
  OModulePresheaf.IterCech.augTot_single_eq_augCech_cup_zero πℤ πℤ topCover topCover
    haff_topCover hcov_topCover ⟨(0, 0), rfl⟩ ⟨α, d_topCover_eq_zero α⟩ ⟨β, d_topCover_eq_zero β⟩
