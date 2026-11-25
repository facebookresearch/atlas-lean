/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGodementTensorPairing
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.FaceComposition
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.Crossover
public import MathlibExt.Algebra.Category.Grp.MonoidalPreadditive
public import MathlibExt.Algebra.Homology.GradedPairingHomology

/-!
# The actual cup on original Godement cochains

The original front and back simplex maps and the actual Godement tensor
pairing construct the Alexander–Whitney cochain cup.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped BigOperators TensorProduct

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- The actual Godement cochain cup uses the original front/back simplex inclusions and tensor
pairing. -/
def smallEtaleGodementCochainCup (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (p q : ℕ) :
    AddCommGrpCat.of
        ((smallEtaleGodementSectionsComplex.{u, w} X F).X p ⊗[ℤ]
          (smallEtaleGodementSectionsComplex.{u, w} X G).X q) ⟶
      (smallEtaleGodementSectionsComplex.{u, w} X (smallEtaleTensorSheaf.{u, w} X F G)).X (p + q) :=
  let A := smallEtaleGodementCoresolution.{u, w} X F
  let B := smallEtaleGodementCoresolution.{u, w} X G
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
  let f := A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion p q (p + q) rfl)
  let g := B.map (AlgebraicTopology.AlexanderWhitney.backInclusion p q (p + q) rfl)
  AddCommGrpCat.ofHom (TensorProduct.map (Γ.map f).hom.toIntLinearMap
      (Γ.map g).hom.toIntLinearMap).toAddMonoidHom ≫
    smallEtaleGammaTensorMap.{u, w} X (A.obj (SimplexCategory.mk (p + q)))
      (B.obj (SimplexCategory.mk (p + q))) ≫
      Γ.map (smallEtaleGodementCoresolutionTensorPairing.{u, w} X F G (p + q))

namespace CosimplicialCup

open MonoidalCategory

universe vC uC
variable {C : Type uC} [Category.{vC} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]
variable (A B D : CosimplicialObject C)
variable (m : ∀ n, A.obj (SimplexCategory.mk n) ⊗ B.obj (SimplexCategory.mk n) ⟶
  D.obj (SimplexCategory.mk n))
variable (hm : ∀ n (i : Fin (n + 2)),
  (A.δ i ⊗ₘ B.δ i) ≫ m (n + 1) = m n ≫ D.δ i)

private def awPair (p q : ℕ) :
    A.obj (SimplexCategory.mk p) ⊗ B.obj (SimplexCategory.mk q) ⟶
      D.obj (SimplexCategory.mk (p + q)) :=
  (A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion p q (p + q) rfl) ⊗ₘ
    B.map (AlgebraicTopology.AlexanderWhitney.backInclusion p q (p + q) rfl)) ≫ m (p + q)

include hm

omit [Preadditive C] [MonoidalPreadditive C] in
set_option backward.isDefEq.respectTransparency.types false in
private theorem awPair_comp_delta_left (p q : ℕ) (i : Fin (p + 1)) :
    awPair A B D m p q ≫ D.δ (⟨i.val, by omega⟩ : Fin (p + q + 2)) =
      (A.δ i.castSucc ⊗ₘ 𝟙 (B.obj (SimplexCategory.mk q))) ≫
        (A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion (p + 1) q (p + q + 1)
            (by omega)) ⊗ₘ
          B.map (AlgebraicTopology.AlexanderWhitney.backInclusion (p + 1) q (p + q + 1)
              (by omega))) ≫
            m (p + q + 1) := by
  let j : Fin (p + q + 2) := ⟨i.val, by omega⟩
  have hf : A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion p q (p + q) rfl) ≫ A.δ j =
      A.δ i.castSucc ≫ A.map
        (AlgebraicTopology.AlexanderWhitney.frontInclusion (p + 1) q (p + q + 1) (by omega)) := by
    exact (A.map_comp _ _).symm.trans
      ((congrArg A.map
        (AlgebraicTopology.AlexanderWhitney.frontInclusion_comp_delta p q i.castSucc).symm).trans
          (A.map_comp _ _))
  have hg : B.map (AlgebraicTopology.AlexanderWhitney.backInclusion p q (p + q) rfl) ≫ B.δ j =
      B.map (AlgebraicTopology.AlexanderWhitney.backInclusion (p + 1) q (p + q + 1) (by omega)) :=
    (B.map_comp _ _).symm.trans
      (congrArg B.map (AlgebraicTopology.AlexanderWhitney.backInclusion_succ_left p q i).symm)
  unfold awPair
  rw [Category.assoc, ← hm (p + q) j, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, hf, hg]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.id_comp]


omit [Preadditive C] [MonoidalPreadditive C] in
set_option backward.isDefEq.respectTransparency.types false in
private theorem awPair_comp_delta_right (p q : ℕ) (j : Fin (q + 1)) :
    awPair A B D m p q ≫ D.δ (⟨p + 1 + j.val, by omega⟩ : Fin (p + q + 2)) =
      (𝟙 (A.obj (SimplexCategory.mk p)) ⊗ₘ B.δ j.succ) ≫
        (A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion p (q + 1) (p + q + 1)
            (by omega)) ⊗ₘ
          B.map (AlgebraicTopology.AlexanderWhitney.backInclusion p (q + 1) (p + q + 1)
              (by omega))) ≫
            m (p + q + 1) := by
  let i : Fin (p + q + 2) := ⟨p + 1 + j.val, by omega⟩
  have hf : A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion p q (p + q) rfl) ≫ A.δ i =
      A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion p (q + 1) (p + q + 1) (by omega)) :=
    (A.map_comp _ _).symm.trans
      (congrArg A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion_succ_right p q j).symm)
  have hg : B.map (AlgebraicTopology.AlexanderWhitney.backInclusion p q (p + q) rfl) ≫ B.δ i =
      B.δ j.succ ≫ B.map
        (AlgebraicTopology.AlexanderWhitney.backInclusion p (q + 1) (p + q + 1) (by omega)) := by
    have he : (⟨p + j.succ.val, by omega⟩ : Fin (p + q + 2)) = i := by
      apply Fin.ext
      change p + (j.val + 1) = p + 1 + j.val
      omega
    have hi : SimplexCategory.δ j.succ ≫
        AlgebraicTopology.AlexanderWhitney.backInclusion p (q + 1) (p + q + 1) (by omega) =
      AlgebraicTopology.AlexanderWhitney.backInclusion p q (p + q) rfl ≫ SimplexCategory.δ i :=
      (AlgebraicTopology.AlexanderWhitney.backInclusion_comp_delta p q j.succ).trans
        (congrArg (fun k => AlgebraicTopology.AlexanderWhitney.backInclusion p q (p + q) rfl ≫
          SimplexCategory.δ k) he)
    exact (B.map_comp _ _).symm.trans ((congrArg B.map hi.symm).trans (B.map_comp _ _))

  unfold awPair
  rw [Category.assoc, ← hm (p + q) i, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, hf, hg]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.id_comp]

omit hm [Preadditive C] [MonoidalPreadditive C] in
set_option backward.isDefEq.respectTransparency.types false in
private theorem awPair_crossover (p q : ℕ) :
    (A.δ (Fin.last (p + 1)) ⊗ₘ 𝟙 (B.obj (SimplexCategory.mk q))) ≫
        (A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion (p + 1) q (p + q + 1)
            (by omega)) ⊗ₘ
          B.map (AlgebraicTopology.AlexanderWhitney.backInclusion (p + 1) q (p + q + 1)
              (by omega))) ≫
            m (p + q + 1) =
      (𝟙 (A.obj (SimplexCategory.mk p)) ⊗ₘ B.δ (0 : Fin (q + 2))) ≫
        (A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion p (q + 1) (p + q + 1)
            (by omega)) ⊗ₘ
          B.map (AlgebraicTopology.AlexanderWhitney.backInclusion p (q + 1) (p + q + 1)
              (by omega))) ≫
            m (p + q + 1) := by
  have hf : A.δ (Fin.last (p + 1)) ≫
        A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion (p + 1) q (p + q + 1) (by omega)) =
      A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion p (q + 1) (p + q + 1) (by omega)) :=
    (A.map_comp _ _).symm.trans
      (congrArg A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion_last_crossover p q))
  have hg :
      B.map (AlgebraicTopology.AlexanderWhitney.backInclusion (p + 1) q (p + q + 1) (by omega)) =
      B.δ (0 : Fin (q + 2)) ≫
        B.map (AlgebraicTopology.AlexanderWhitney.backInclusion p (q + 1) (p + q + 1) (by omega)) :=
    (congrArg B.map (AlgebraicTopology.AlexanderWhitney.backInclusion_zero_crossover p q)).trans
      (B.map_comp _ _)
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.id_comp]
  rw [hf, hg]

set_option backward.isDefEq.respectTransparency.types false in
private theorem awPair_leibniz (p q : ℕ) :
    awPair A B D m p q ≫ AlternatingCofaceMapComplex.objD D (p + q) =
      (AlternatingCofaceMapComplex.objD A p ⊗ₘ 𝟙 (B.obj (SimplexCategory.mk q))) ≫
        (A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion (p + 1) q (p + q + 1)
            (by omega)) ⊗ₘ
          B.map (AlgebraicTopology.AlexanderWhitney.backInclusion (p + 1) q (p + q + 1)
              (by omega))) ≫
            m (p + q + 1) +
      ((-1 : ℤ) ^ p) •
        ((𝟙 (A.obj (SimplexCategory.mk p)) ⊗ₘ AlternatingCofaceMapComplex.objD B q) ≫
          (A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion p (q + 1) (p + q + 1)
              (by omega)) ⊗ₘ
            B.map (AlgebraicTopology.AlexanderWhitney.backInclusion p (q + 1) (p + q + 1)
                (by omega))) ≫
              m (p + q + 1)) := by
  let l (i : Fin (p + 2)) := (A.δ i ⊗ₘ 𝟙 (B.obj (SimplexCategory.mk q))) ≫
    (A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion (p + 1) q (p + q + 1) (by omega)) ⊗ₘ
      B.map (AlgebraicTopology.AlexanderWhitney.backInclusion (p + 1) q (p + q + 1) (by omega))) ≫
          m (p + q + 1)
  let r (j : Fin (q + 2)) := (𝟙 (A.obj (SimplexCategory.mk p)) ⊗ₘ B.δ j) ≫
    (A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion p (q + 1) (p + q + 1) (by omega)) ⊗ₘ
      B.map (AlgebraicTopology.AlexanderWhitney.backInclusion p (q + 1) (p + q + 1) (by omega))) ≫
          m (p + q + 1)
  have hx : l (Fin.last (p + 1)) = r 0 := awPair_crossover A B D m p q
  have hl (i : Fin (p + 1)) : awPair A B D m p q ≫
      D.δ (⟨i.val, by omega⟩ : Fin (p + q + 2)) = l i.castSucc :=
    awPair_comp_delta_left A B D m hm p q i
  have hr (j : Fin (q + 1)) : awPair A B D m p q ≫
      D.δ (⟨p + 1 + j.val, by omega⟩ : Fin (p + q + 2)) = r j.succ :=
    awPair_comp_delta_right A B D m hm p q j
  let z (i : Fin (p + q + 2)) := (-1 : ℤ) ^ i.val •
    (awPair A B D m p q ≫ D.δ i)
  have hz : (∑ i : Fin (p + q + 2), z i) =
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ i.val • l i.castSucc) +
        ∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) • r j.succ := by
    let f : Fin ((p + 1) + (q + 1)) → (A.obj (SimplexCategory.mk p) ⊗ B.obj (SimplexCategory.mk q) ⟶
      D.obj (SimplexCategory.mk (p + q + 1))) := fun i => z (i.cast (by omega))
    have hsplit := Fin.sum_univ_add f
    have he : (∑ i, f i) = ∑ i, z i := Fin.sum_congr' z (by omega)
    rw [he] at hsplit
    refine hsplit.trans (congrArg₂ (· + ·) ?_ ?_)
    · apply Finset.sum_congr rfl
      intro i _
      dsimp only [f, z]
      have hi : ((i.castAdd (q + 1)).cast (by omega) : Fin (p + q + 2)) =
          (⟨i.val, by omega⟩ : Fin (p + q + 2)) := by apply Fin.ext; rfl
      rw [hi, hl]
    · apply Finset.sum_congr rfl
      intro j _
      dsimp only [f, z]
      have hj : ((j.natAdd (p + 1)).cast (by omega) : Fin (p + q + 2)) =
          (⟨p + 1 + j.val, by omega⟩ : Fin (p + q + 2)) := by apply Fin.ext; rfl
      rw [hj, hr]
  have hsign (j : Fin (q + 1)) :
      (-1 : ℤ) ^ (p + 1 + j.val) • r j.succ =
        (-1 : ℤ) ^ p • ((-1 : ℤ) ^ j.succ.val • r j.succ) := by
    rw [smul_smul, ← pow_add]
    congr 2
    simp only [Fin.val_succ]
    omega
  have hc : (-1 : ℤ) ^ (p + 1) • l (Fin.last (p + 1)) +
      (-1 : ℤ) ^ p • r 0 = 0 := by
    rw [hx, pow_succ, mul_neg_one, neg_smul]
    exact neg_add_cancel _
  change awPair A B D m p q ≫ (∑ i : Fin (p + q + 2), (-1 : ℤ) ^ i.val • D.δ i) = _
  rw [Preadditive.comp_sum]
  simp_rw [Preadditive.comp_zsmul]
  change (∑ i, z i) = _
  rw [hz]
  let L : (A.obj (SimplexCategory.mk p) ⟶ A.obj (SimplexCategory.mk (p + 1))) →+
      (A.obj (SimplexCategory.mk p) ⊗ B.obj (SimplexCategory.mk q) ⟶
          D.obj (SimplexCategory.mk (p + q + 1))) :=
    { toFun := fun f => (f ⊗ₘ 𝟙 _) ≫
        (A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion (p + 1) q (p + q + 1)
            (by omega)) ⊗ₘ
          B.map (AlgebraicTopology.AlexanderWhitney.backInclusion (p + 1) q (p + q + 1)
              (by omega))) ≫ m (p + q + 1)
      map_zero' := by simp
      map_add' := by intros; simp only [MonoidalPreadditive.add_tensor, Preadditive.add_comp] }
  let R : (B.obj (SimplexCategory.mk q) ⟶ B.obj (SimplexCategory.mk (q + 1))) →+
      (A.obj (SimplexCategory.mk p) ⊗ B.obj (SimplexCategory.mk q) ⟶
          D.obj (SimplexCategory.mk (p + q + 1))) :=
    { toFun := fun f => (𝟙 _ ⊗ₘ f) ≫
        (A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion p (q + 1) (p + q + 1)
            (by omega)) ⊗ₘ
          B.map (AlgebraicTopology.AlexanderWhitney.backInclusion p (q + 1) (p + q + 1)
              (by omega))) ≫ m (p + q + 1)
      map_zero' := by simp
      map_add' := by intros; simp only [MonoidalPreadditive.tensor_add, Preadditive.add_comp] }
  have hL : L (∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val • A.δ i) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val • l i := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact L.map_zsmul ((-1 : ℤ) ^ i.val) (A.δ i)
  have hR : R (∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val • B.δ j) =
      ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val • r j := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact R.map_zsmul ((-1 : ℤ) ^ j.val) (B.δ j)
  change _ = L (∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val • A.δ i) +
    (-1 : ℤ) ^ p • R (∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val • B.δ j)
  rw [hL, hR]
  have hls : (∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val • l i) =
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ i.val • l i.castSucc) +
        (-1 : ℤ) ^ (p + 1) • l (Fin.last (p + 1)) :=
    Fin.sum_univ_castSucc _
  have hrs : (∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val • r j) =
      r 0 + ∑ j : Fin (q + 1), (-1 : ℤ) ^ j.succ.val • r j.succ := by
    have h := Fin.sum_univ_succ (fun j : Fin (q + 2) => (-1 : ℤ) ^ j.val • r j)
    simpa only [Fin.val_zero, pow_zero, one_zsmul] using h
  rw [hls, hrs, smul_add, Finset.smul_sum]
  have hs : (∑ j : Fin (q + 1), (-1 : ℤ) ^ p • ((-1 : ℤ) ^ j.succ.val • r j.succ)) =
      ∑ j : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + j.val) • r j.succ := by
    apply Finset.sum_congr rfl
    intro j _
    exact (hsign j).symm
  rw [hs]
  have hn : (-1 : ℤ) ^ (p + 1) • l (Fin.last (p + 1)) = -((-1 : ℤ) ^ p • r 0) :=
    eq_neg_of_add_eq_zero_left hc
  rw [hn]
  abel

end CosimplicialCup

/-- Original global sections applied degreewise to the genuine Godement cosimplicial object. -/
def smallEtaleGodementSectionsCosimplicial (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    CosimplicialObject AddCommGrpCat.{max u w} :=
  smallEtaleGodementCoresolution.{u, w} X F ⋙
    Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}

/-- The actual binary tensor map on the same global-section cosimplicial objects. -/
def smallEtaleGodementSectionsDegreePairing (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    AddCommGrpCat.of
        ((smallEtaleGodementSectionsCosimplicial.{u, w} X F).obj (SimplexCategory.mk n) ⊗[ℤ]
          (smallEtaleGodementSectionsCosimplicial.{u, w} X G).obj (SimplexCategory.mk n)) ⟶
      (smallEtaleGodementSectionsCosimplicial.{u, w} X (smallEtaleTensorSheaf.{u, w} X F G)).obj
        (SimplexCategory.mk n) :=
  smallEtaleGammaTensorMap.{u, w} X
      ((smallEtaleGodementCoresolution.{u, w} X F).obj (SimplexCategory.mk n))
      ((smallEtaleGodementCoresolution.{u, w} X G).obj (SimplexCategory.mk n)) ≫
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map
      (smallEtaleGodementCoresolutionTensorPairing.{u, w} X F G n)

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual global-section degree pairing commutes with every original Godement coface. -/
theorem smallEtaleGodementSectionsDegreePairing_coface (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) (i : Fin (n + 2)) :
    AddCommGrpCat.ofHom (TensorProduct.map
        ((smallEtaleGodementSectionsCosimplicial.{u, w} X F).δ i).hom.toIntLinearMap
        ((smallEtaleGodementSectionsCosimplicial.{u, w} X G).δ
            i).hom.toIntLinearMap).toAddMonoidHom ≫
      smallEtaleGodementSectionsDegreePairing.{u, w} X F G (n + 1) =
      smallEtaleGodementSectionsDegreePairing.{u, w} X F G n ≫
        (smallEtaleGodementSectionsCosimplicial.{u, w} X
            (smallEtaleTensorSheaf.{u, w} X F G)).δ i := by
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
  let A := smallEtaleGodementCoresolution.{u, w} X F
  let B := smallEtaleGodementCoresolution.{u, w} X G
  let D := smallEtaleGodementCoresolution.{u, w} X (smallEtaleTensorSheaf.{u, w} X F G)
  let t n := smallEtaleGammaTensorMap.{u, w} X (A.obj (SimplexCategory.mk n))
      (B.obj (SimplexCategory.mk n))
  let m n := smallEtaleGodementCoresolutionTensorPairing.{u, w} X F G n
  let a := AddCommGrpCat.ofHom (TensorProduct.map
    (Γ.map (A.δ i)).hom.toIntLinearMap (Γ.map (B.δ i)).hom.toIntLinearMap).toAddMonoidHom
  let b := smallEtaleTensorSheafMap.{u, w} X (A.δ i) (B.δ i)
  have ht : a ≫ t (n + 1) = t n ≫ Γ.map b :=
    smallEtaleGammaTensorMap_naturality.{u, w} X (A.δ i) (B.δ i)
  have hm : b ≫ m (n + 1) = m n ≫ D.δ i :=
    smallEtaleGodementCoresolutionTensorPairing_coface.{u, w} X F G n i
  change a ≫ (t (n + 1) ≫ Γ.map (m (n + 1))) = (t n ≫ Γ.map (m n)) ≫ Γ.map (D.δ i)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun l => l ≫ Γ.map (m (n + 1))) ht).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun l => t n ≫ l)
          ((Γ.map_comp b (m (n + 1))).symm.trans
            ((congrArg Γ.map hm).trans (Γ.map_comp (m n) (D.δ i))))).trans
              (Category.assoc _ _ _).symm)))

set_option backward.isDefEq.respectTransparency.types false in
private theorem additiveAlternatingCofaceDifferential.{vC, uC, vD, uD}
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (A : CosimplicialObject C) (n : ℕ) :
    F.map (AlternatingCofaceMapComplex.objD A n) =
      AlternatingCofaceMapComplex.objD (A ⋙ F) n := by
  let a := fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val • A.δ i
  have h := _root_.map_sum (F.mapAddHom : (A.obj (SimplexCategory.mk n) ⟶
      A.obj (SimplexCategory.mk (n + 1))) →+ (F.obj (A.obj (SimplexCategory.mk n)) ⟶
        F.obj (A.obj (SimplexCategory.mk (n + 1))))) a Finset.univ
  have h' : F.map (∑ i, a i) = ∑ i, F.map (a i) := h
  change F.map (∑ i, a i) = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • F.map (A.δ i)
  rw [h']
  apply Finset.sum_congr rfl
  intro i _
  exact F.map_zsmul

set_option backward.isDefEq.respectTransparency.types false in
theorem additiveAlternatingCofaceComm.{vC, uC, vD, uD}
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    {D : Type uD} [Category.{vD} D] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (A : CosimplicialObject C) (i j : ℕ)
    (hij : (ComplexShape.up ℕ).Rel i j) :
    (Iso.refl ((AlternatingCofaceMapComplex.obj (A ⋙ F)).X i)).hom ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (AlternatingCofaceMapComplex.obj A)).d i j =
      (AlternatingCofaceMapComplex.obj (A ⋙ F)).d i j ≫
        (Iso.refl ((AlternatingCofaceMapComplex.obj (A ⋙ F)).X j)).hom := by
  obtain rfl : i + 1 = j := hij
  dsimp only [AlternatingCofaceMapComplex.obj, Functor.mapHomologicalComplex_obj_d,
    Iso.refl_hom]
  rw [CochainComplex.of_d, CochainComplex.of_d, Category.id_comp, Category.comp_id]
  exact additiveAlternatingCofaceDifferential F A i

/-- The actual alternating global-section complex is the original Godement sections complex. -/
def smallEtaleGodementAlternatingSectionsIso (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    AlternatingCofaceMapComplex.obj (smallEtaleGodementSectionsCosimplicial.{u, w} X F) ≅
      smallEtaleGodementSectionsComplex.{u, w} X F :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (fun i j hij => additiveAlternatingCofaceComm
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w})
      (smallEtaleGodementCoresolution.{u, w} X F) i j hij)

open MonoidalCategory

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual global-section cosimplicial pairing induces the original alternating cochain
pairing. -/
def smallEtaleGodementAlternatingGradedPairing (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    HomologicalComplex.CochainGradedPairing
      (AlternatingCofaceMapComplex.obj (smallEtaleGodementSectionsCosimplicial.{u, w} X F))
      (AlternatingCofaceMapComplex.obj (smallEtaleGodementSectionsCosimplicial.{u, w} X G))
      (AlternatingCofaceMapComplex.obj
        (smallEtaleGodementSectionsCosimplicial.{u, w} X
            (smallEtaleTensorSheaf.{u, w} X F G))) where
  pair p q :=
    ((smallEtaleGodementSectionsCosimplicial.{u, w} X F).map
        (AlexanderWhitney.frontInclusion p q (p + q) rfl) ⊗ₘ
      (smallEtaleGodementSectionsCosimplicial.{u, w} X G).map
        (AlexanderWhitney.backInclusion p q (p + q) rfl)) ≫
      smallEtaleGodementSectionsDegreePairing.{u, w} X F G (p + q)
  leibniz p q := by
    let A := smallEtaleGodementSectionsCosimplicial.{u, w} X F
    let B := smallEtaleGodementSectionsCosimplicial.{u, w} X G
    let D := smallEtaleGodementSectionsCosimplicial.{u, w} X (smallEtaleTensorSheaf.{u, w} X F G)
    let m := smallEtaleGodementSectionsDegreePairing.{u, w} X F G
    have hm : ∀ n (i : Fin (n + 2)), (A.δ i ⊗ₘ B.δ i) ≫ m (n + 1) = m n ≫ D.δ i :=
      fun n i => smallEtaleGodementSectionsDegreePairing_coface.{u, w} X F G n i
    have h := CosimplicialCup.awPair_leibniz A B D m hm p q
    have he (a b n : ℕ) (hab : a + b = n) :
        CosimplicialCup.awPair A B D m a b ≫
          ((AlternatingCofaceMapComplex.obj D).XIsoOfEq hab).hom =
        (A.map (AlgebraicTopology.AlexanderWhitney.frontInclusion a b n hab) ⊗ₘ
          B.map (AlgebraicTopology.AlexanderWhitney.backInclusion a b n hab)) ≫ m n := by
      subst n
      rw [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
      change CosimplicialCup.awPair A B D m a b ≫ (𝟙 (D.obj (SimplexCategory.mk (a + b)))) = _
      exact Category.comp_id _
    dsimp only [AlternatingCofaceMapComplex.obj]
    rw [CochainComplex.of_d, CochainComplex.of_d, CochainComplex.of_d]
    have hleft := he (p + 1) q (p + q + 1) (by omega)
    have hright := he p (q + 1) (p + q + 1) (by omega)
    change CosimplicialCup.awPair A B D m p q ≫ AlternatingCofaceMapComplex.objD D (p + q) =
      (AlternatingCofaceMapComplex.objD A p ⊗ₘ 𝟙 _) ≫
        (CosimplicialCup.awPair A B D m (p + 1) q ≫ _) +
      (-1 : ℤ) ^ p • ((𝟙 _ ⊗ₘ AlternatingCofaceMapComplex.objD B q) ≫
        (CosimplicialCup.awPair A B D m p (q + 1) ≫ _))
    have hh : (AlternatingCofaceMapComplex.objD A p ⊗ₘ 𝟙 (B.obj (SimplexCategory.mk q))) ≫
          (CosimplicialCup.awPair A B D m (p + 1) q ≫
            ((AlternatingCofaceMapComplex.obj D).XIsoOfEq
                (show (p + 1) + q = p + q + 1 by omega)).hom) =
        (AlternatingCofaceMapComplex.objD A p ⊗ₘ 𝟙 (B.obj (SimplexCategory.mk q))) ≫
          ((A.map (AlexanderWhitney.frontInclusion (p + 1) q (p + q + 1) (by omega)) ⊗ₘ
            B.map (AlexanderWhitney.backInclusion (p + 1) q (p + q + 1) (by omega))) ≫
                m (p + q + 1)) :=
      congrArg (fun l => (AlternatingCofaceMapComplex.objD A p ⊗ₘ
          𝟙 (B.obj (SimplexCategory.mk q))) ≫ l) hleft
    have hk := congrArg (fun l => (-1 : ℤ) ^ p •
      ((𝟙 (A.obj (SimplexCategory.mk p)) ⊗ₘ AlternatingCofaceMapComplex.objD B q) ≫ l)) hright
    exact h.trans (congrArg₂ (· + ·) hh hk).symm


/-- The actual cup pairing on the original Godement sections complexes. -/
def smallEtaleGodementGradedPairing (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    HomologicalComplex.CochainGradedPairing
      (smallEtaleGodementSectionsComplex.{u, w} X F)
      (smallEtaleGodementSectionsComplex.{u, w} X G)
      (smallEtaleGodementSectionsComplex.{u, w} X (smallEtaleTensorSheaf.{u, w} X F G)) :=
  (smallEtaleGodementAlternatingGradedPairing.{u, w} X F G).whisker
    (smallEtaleGodementAlternatingSectionsIso.{u, w} X F).inv
    (smallEtaleGodementAlternatingSectionsIso.{u, w} X G).inv
    (smallEtaleGodementAlternatingSectionsIso.{u, w} X (smallEtaleTensorSheaf.{u, w} X F G)).hom

set_option backward.isDefEq.respectTransparency.types false in
/-- The constructed graded pairing has the same literal original cochain cup component. -/
theorem smallEtaleGodementGradedPairing_pair (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (p q : ℕ) :
    (smallEtaleGodementGradedPairing.{u, w} X F G).pair p q =
      smallEtaleGodementCochainCup.{u, w} X F G p q := by
  change ((𝟙 _) ⊗ₘ (𝟙 _)) ≫ _ ≫ (𝟙 _) = _
  rw [MonoidalCategory.id_tensorHom_id, Category.id_comp]
  let A := smallEtaleGodementSectionsCosimplicial.{u, w} X F
  let B := smallEtaleGodementSectionsCosimplicial.{u, w} X G
  let m := smallEtaleGodementSectionsDegreePairing.{u, w} X F G (p + q)
  change ((A.map (AlexanderWhitney.frontInclusion p q (p + q) rfl) ⊗ₘ
    B.map (AlexanderWhitney.backInclusion p q (p + q) rfl)) ≫ m) ≫
      (𝟙 _) = smallEtaleGodementCochainCup.{u, w} X F G p q
  exact (Category.comp_id _).trans (Category.assoc _ _ _).symm

/-- The actual Godement cup descends to the same original resolution homology objects. -/
def smallEtaleGodementHomologyCup (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (p q : ℕ) :
    (smallEtaleGodementSectionsComplex.{u, w} X F).homology p ⊗
        (smallEtaleGodementSectionsComplex.{u, w} X G).homology q ⟶
      (smallEtaleGodementSectionsComplex.{u, w} X
          (smallEtaleTensorSheaf.{u, w} X F G)).homology (p + q) :=
  (smallEtaleGodementGradedPairing.{u, w} X F G).pairHomology p q

/-- The original étale cup map uses the actual tensor coefficient and original Sheaf.H groups. -/
def originalSmallEtaleCupTensorMap (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (p q : ℕ) :
    AddCommGrpCat.of (Sheaf.H.{max u w, max u w, u, u + 1} F p ⊗[ℤ]
        Sheaf.H.{max u w, max u w, u, u + 1} G q) ⟶
      AddCommGrpCat.of (Sheaf.H.{max u w, max u w, u, u + 1}
        (smallEtaleTensorSheaf.{u, w} X F G) (p + q)) :=
  AddCommGrpCat.ofHom (TensorProduct.map
      (smallEtaleGodementCohomologyAddEquiv.{u, w} X F p).toAddMonoidHom.toIntLinearMap
      (smallEtaleGodementCohomologyAddEquiv.{u, w} X G
          q).toAddMonoidHom.toIntLinearMap).toAddMonoidHom ≫
    smallEtaleGodementHomologyCup.{u, w} X F G p q ≫
      AddCommGrpCat.ofHom (smallEtaleGodementCohomologyAddEquiv.{u, w} X
        (smallEtaleTensorSheaf.{u, w} X F G) (p + q)).symm.toAddMonoidHom

/-- The original étale cohomology cup evaluated on two original classes. -/
abbrev originalSmallEtaleCup (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (p q : ℕ)
    (a : Sheaf.H.{max u w, max u w, u, u + 1} F p)
    (b : Sheaf.H.{max u w, max u w, u, u + 1} G q) :
    Sheaf.H.{max u w, max u w, u, u + 1} (smallEtaleTensorSheaf.{u, w} X F G) (p + q) :=
  (originalSmallEtaleCupTensorMap.{u, w} X F G p q).hom (a ⊗ₜ[ℤ] b)

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual cup of original Godement cycle classes is the class of the constructed paired
cycle. -/
theorem smallEtaleGodementHomologyCup_pi (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (p q : ℕ) :
    let A := smallEtaleGodementSectionsComplex.{u, w} X F
    let B := smallEtaleGodementSectionsComplex.{u, w} X G
    let D := smallEtaleGodementSectionsComplex.{u, w} X (smallEtaleTensorSheaf.{u, w} X F G)
    (A.homologyπ p ⊗ₘ B.homologyπ q) ≫ smallEtaleGodementHomologyCup.{u, w} X F G p q =
      (smallEtaleGodementGradedPairing.{u, w} X F G).pairCycles p q ≫ D.homologyπ (p + q) := by
  intro A B D
  exact (smallEtaleGodementGradedPairing.{u, w} X F G).tensor_homologyπ_comp_pairHomology p q

private theorem tensorAddMapLeft.{a, b, c}
    {A : Type a} {B : Type b} {D : Type c} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    (f : A ⊗[ℤ] B →+ D) (x y : A) (z : B) :
    f ((x + y) ⊗ₜ[ℤ] z) = f (x ⊗ₜ[ℤ] z) + f (y ⊗ₜ[ℤ] z) :=
  (congrArg f (TensorProduct.add_tmul x y z)).trans (f.map_add _ _)

private theorem tensorAddMapRight.{a, b, c}
    {A : Type a} {B : Type b} {D : Type c} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    (f : A ⊗[ℤ] B →+ D) (x : A) (y z : B) :
    f (x ⊗ₜ[ℤ] (y + z)) = f (x ⊗ₜ[ℤ] y) + f (x ⊗ₜ[ℤ] z) :=
  (congrArg f (TensorProduct.tmul_add x y z)).trans (f.map_add _ _)

set_option backward.isDefEq.respectTransparency.types false in
/-- The original étale cup preserves addition in its left class argument. -/
theorem originalSmallEtaleCup_add_left (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (p q : ℕ)
    (a a' : Sheaf.H.{max u w, max u w, u, u + 1} F p)
    (b : Sheaf.H.{max u w, max u w, u, u + 1} G q) :
    let f := (originalSmallEtaleCupTensorMap.{u, w} X F G p q).hom
    f ((a + a') ⊗ₜ[ℤ] b) = f (a ⊗ₜ[ℤ] b) + f (a' ⊗ₜ[ℤ] b) := by
  intro f
  exact (congrArg (fun t => f t) (TensorProduct.add_tmul a a' b)).trans
    (f.map_add (a ⊗ₜ[ℤ] b) (a' ⊗ₜ[ℤ] b))

set_option backward.isDefEq.respectTransparency.types false in
/-- The original étale cup preserves addition in its right class argument. -/
theorem originalSmallEtaleCup_add_right (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (p q : ℕ)
    (a : Sheaf.H.{max u w, max u w, u, u + 1} F p)
    (b b' : Sheaf.H.{max u w, max u w, u, u + 1} G q) :
    let f := (originalSmallEtaleCupTensorMap.{u, w} X F G p q).hom
    f (a ⊗ₜ[ℤ] (b + b')) = f (a ⊗ₜ[ℤ] b) + f (a ⊗ₜ[ℤ] b') := by
  intro f
  exact (congrArg (fun t => f t) (TensorProduct.tmul_add a b b')).trans
    (f.map_add (a ⊗ₜ[ℤ] b) (a ⊗ₜ[ℤ] b'))

/-- Every original coefficient map induces the actual map of Godement sections complexes. -/
def smallEtaleGodementSectionsMap (X : Scheme.{u})
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}} (f : F ⟶ G) :
    smallEtaleGodementSectionsComplex.{u, w} X F ⟶ smallEtaleGodementSectionsComplex.{u, w} X G :=
  ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
    ((alternatingCofaceMapComplex _).map
      ((Monad.coresolutionFunctor (smallEtaleGodementMonad.{u, w} X)).map f))

/-- The same original coefficient map acts through literal monad powers in every Godement degree. -/
theorem smallEtaleGodementSectionsMap_degree (X : Scheme.{u})
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}} (f : F ⟶ G) (n : ℕ) :
    (smallEtaleGodementSectionsMap.{u, w} X f).f n =
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).map
        (((Monad.coresolutionFunctor (smallEtaleGodementMonad.{u, w} X)).map f).app
          (SimplexCategory.mk n)) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual global-section degree pairing is natural in every original coefficient map. -/
theorem smallEtaleGodementSectionsDegreePairing_naturality (X : Scheme.{u})
    {F F' G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') (n : ℕ) :
    AddCommGrpCat.ofHom (TensorProduct.map
        ((smallEtaleGodementSectionsMap.{u, w} X f).f n).hom.toIntLinearMap
        ((smallEtaleGodementSectionsMap.{u, w} X g).f n).hom.toIntLinearMap).toAddMonoidHom ≫
      smallEtaleGodementSectionsDegreePairing.{u, w} X F' G' n =
      smallEtaleGodementSectionsDegreePairing.{u, w} X F G n ≫
        (smallEtaleGodementSectionsMap.{u, w} X (smallEtaleTensorSheafMap.{u, w} X f g)).f n := by
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
  let T := smallEtaleGodementMonad.{u, w} X
  let a := ((Monad.coresolutionFunctor T).map f).app (SimplexCategory.mk n)
  let b := ((Monad.coresolutionFunctor T).map g).app (SimplexCategory.mk n)
  let c := ((Monad.coresolutionFunctor T).map (smallEtaleTensorSheafMap.{u, w} X f g)).app
      (SimplexCategory.mk n)
  let t := smallEtaleGammaTensorMap.{u, w} X
    ((smallEtaleGodementCoresolution.{u, w} X F).obj (SimplexCategory.mk n))
    ((smallEtaleGodementCoresolution.{u, w} X G).obj (SimplexCategory.mk n))
  let t' := smallEtaleGammaTensorMap.{u, w} X
    ((smallEtaleGodementCoresolution.{u, w} X F').obj (SimplexCategory.mk n))
    ((smallEtaleGodementCoresolution.{u, w} X G').obj (SimplexCategory.mk n))
  let m := smallEtaleGodementCoresolutionTensorPairing.{u, w} X F G n
  let m' := smallEtaleGodementCoresolutionTensorPairing.{u, w} X F' G' n
  let s := AddCommGrpCat.ofHom (TensorProduct.map (Γ.map a).hom.toIntLinearMap
    (Γ.map b).hom.toIntLinearMap).toAddMonoidHom
  let v := smallEtaleTensorSheafMap.{u, w} X a b
  have ht : s ≫ t' = t ≫ Γ.map v := smallEtaleGammaTensorMap_naturality.{u, w} X a b
  have hm : v ≫ m' = m ≫ c := smallEtaleGodementCoresolutionTensorPairing_naturality.{u, w} X f g n
  change s ≫ (t' ≫ Γ.map m') = (t ≫ Γ.map m) ≫ Γ.map c
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun l => l ≫ Γ.map m') ht).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun l => t ≫ l)
          ((Γ.map_comp v m').symm.trans ((congrArg Γ.map hm).trans (Γ.map_comp m c)))).trans
            (Category.assoc _ _ _).symm)))

namespace CosimplicialCup

universe vC uC
open MonoidalCategory

set_option backward.isDefEq.respectTransparency.types false in
private theorem awPair_naturality
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {A A' B B' D D' : CosimplicialObject C}
    (m : ∀ n,
        A.obj (SimplexCategory.mk n) ⊗ B.obj (SimplexCategory.mk n) ⟶
        D.obj (SimplexCategory.mk n))
    (m' : ∀ n,
        A'.obj (SimplexCategory.mk n) ⊗ B'.obj (SimplexCategory.mk n) ⟶
        D'.obj (SimplexCategory.mk n))
    (f : A ⟶ A') (g : B ⟶ B') (h : D ⟶ D')
    (hm : ∀ n, (f.app (SimplexCategory.mk n) ⊗ₘ g.app (SimplexCategory.mk n)) ≫ m' n =
      m n ≫ h.app (SimplexCategory.mk n)) (p q : ℕ) :
    (f.app (SimplexCategory.mk p) ⊗ₘ g.app (SimplexCategory.mk q)) ≫ awPair A' B' D' m' p q =
      awPair A B D m p q ≫ h.app (SimplexCategory.mk (p + q)) := by
  let F := AlgebraicTopology.AlexanderWhitney.frontInclusion p q (p + q) rfl
  let Bk := AlgebraicTopology.AlexanderWhitney.backInclusion p q (p + q) rfl
  have hf := f.naturality F
  have hg := g.naturality Bk
  unfold awPair
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, ← hf, ← hg,
    ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc, hm, ← Category.assoc]

end CosimplicialCup

/-- The actual original coefficient morphism on global-section Godement cosimplicial objects. -/
def smallEtaleGodementSectionsCosimplicialMap (X : Scheme.{u})
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}} (f : F ⟶ G) :
    smallEtaleGodementSectionsCosimplicial.{u, w} X F ⟶
        smallEtaleGodementSectionsCosimplicial.{u, w} X G :=
  Functor.whiskerRight ((Monad.coresolutionFunctor (smallEtaleGodementMonad.{u, w} X)).map f)
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w})

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual original cochain cup commutes with every original pair of coefficient maps. -/
theorem smallEtaleGodementCochainCup_naturality (X : Scheme.{u})
    {F F' G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') (p q : ℕ) :
    AddCommGrpCat.ofHom (TensorProduct.map
        ((smallEtaleGodementSectionsMap.{u, w} X f).f p).hom.toIntLinearMap
        ((smallEtaleGodementSectionsMap.{u, w} X g).f q).hom.toIntLinearMap).toAddMonoidHom ≫
      smallEtaleGodementCochainCup.{u, w} X F' G' p q =
      smallEtaleGodementCochainCup.{u, w} X F G p q ≫
        (smallEtaleGodementSectionsMap.{u, w} X (smallEtaleTensorSheafMap.{u, w} X f g)).f
            (p + q) := by
  let A := smallEtaleGodementSectionsCosimplicial.{u, w} X F
  let A' := smallEtaleGodementSectionsCosimplicial.{u, w} X F'
  let B := smallEtaleGodementSectionsCosimplicial.{u, w} X G
  let B' := smallEtaleGodementSectionsCosimplicial.{u, w} X G'
  let D := smallEtaleGodementSectionsCosimplicial.{u, w} X (smallEtaleTensorSheaf.{u, w} X F G)
  let D' := smallEtaleGodementSectionsCosimplicial.{u, w} X (smallEtaleTensorSheaf.{u, w} X F' G')
  let m := smallEtaleGodementSectionsDegreePairing.{u, w} X F G
  let m' := smallEtaleGodementSectionsDegreePairing.{u, w} X F' G'
  let a := smallEtaleGodementSectionsCosimplicialMap.{u, w} X f
  let b := smallEtaleGodementSectionsCosimplicialMap.{u, w} X g
  let c := smallEtaleGodementSectionsCosimplicialMap.{u, w} X
      (smallEtaleTensorSheafMap.{u, w} X f g)
  have hm : ∀ n, (a.app (SimplexCategory.mk n) ⊗ₘ b.app (SimplexCategory.mk n)) ≫ m' n =
      m n ≫ c.app (SimplexCategory.mk n) :=
    fun n => smallEtaleGodementSectionsDegreePairing_naturality.{u, w} X f g n
  have h := CosimplicialCup.awPair_naturality m m' a b c hm p q
  exact h

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual native Godement cup is natural on the same original resolution homology objects. -/
theorem smallEtaleGodementHomologyCup_naturality (X : Scheme.{u})
    {F F' G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') (p q : ℕ) :
    (HomologicalComplex.homologyMap (smallEtaleGodementSectionsMap.{u, w} X f) p ⊗ₘ
        HomologicalComplex.homologyMap (smallEtaleGodementSectionsMap.{u, w} X g) q) ≫
      smallEtaleGodementHomologyCup.{u, w} X F' G' p q =
      smallEtaleGodementHomologyCup.{u, w} X F G p q ≫
        HomologicalComplex.homologyMap
          (smallEtaleGodementSectionsMap.{u, w} X (smallEtaleTensorSheafMap.{u, w} X f g))
              (p + q) := by
  let P := smallEtaleGodementGradedPairing.{u, w} X F G
  let Q := smallEtaleGodementGradedPairing.{u, w} X F' G'
  have hp : ∀ p q, P.pair p q ≫
      (smallEtaleGodementSectionsMap.{u, w} X (smallEtaleTensorSheafMap.{u, w} X f g)).f (p + q) =
      ((smallEtaleGodementSectionsMap.{u, w} X f).f p ⊗ₘ
        (smallEtaleGodementSectionsMap.{u, w} X g).f q) ≫ Q.pair p q := by
    intro p q
    have h := smallEtaleGodementCochainCup_naturality.{u, w} X f g p q
    have hP := smallEtaleGodementGradedPairing_pair.{u, w} X F G p q
    have hQ := smallEtaleGodementGradedPairing_pair.{u, w} X F' G' p q
    exact (congrArg (fun l => l ≫
      (smallEtaleGodementSectionsMap.{u, w} X (smallEtaleTensorSheafMap.{u, w} X f g)).f
          (p + q)) hP).trans
      (h.symm.trans (congrArg (fun l => ((smallEtaleGodementSectionsMap.{u, w} X f).f p ⊗ₘ
        (smallEtaleGodementSectionsMap.{u, w} X g).f q) ≫ l) hQ.symm))
  exact HomologicalComplex.CochainGradedPairing.pairHomology_naturality P Q
    (smallEtaleGodementSectionsMap.{u, w} X f) (smallEtaleGodementSectionsMap.{u, w} X g)
    (smallEtaleGodementSectionsMap.{u, w} X (smallEtaleTensorSheafMap.{u, w} X f g)) hp p q

end AlgebraicGeometry.Scheme.DerivedSections
