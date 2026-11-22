/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.DimensionPowerAdd
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.FiniteBijectionStructure
public import MathlibExt.CategoryTheory.Monoidal.SymmetricTensorPower
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Actual finite permutations of native dimension tensor powers

The original tensor permutation of dimension-one factors is the literal
finite-bijection coordinate matrix point after the original dimension equality.
All finite bijections, the empty dimension, source-first composition, ordered
blocks and independent native universes are retained.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open CategoryTheory.MonoidalCategory.SymmetricTensorPower

namespace CategoryTheory.Spectra

attribute [local instance] OrthogonalIndex.enrichedCategory OrthogonalIndex.category
  OrthogonalIndex.monoidalCategory OrthogonalIndex.enrichedOrdinaryCategory
  OrthogonalIndex.symmetricCategory

universe u v

/-- The actual finite-bijection matrix point viewed as a native ordinary index arrow. -/
def dimensionMatrixPoint {m n : OrthogonalIndex}
    (e : Fin m ≃ Fin n) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    m ⟶ n := by
  change 𝟙_ PointedCGWH.{u, v} ⟶ OrthogonalIndex.hom.{u, v} m n
  exact OrthogonalIndex.matrixPoint.{u, v} (finiteBijectionMatrix e)

theorem dimensionMatrixTensor {m n : OrthogonalIndex}
    (e : Equiv.Perm (Fin m)) (f : Equiv.Perm (Fin n)) :
    dimensionMatrixPoint.{u, v} e ⊗ₘ dimensionMatrixPoint.{u, v} f =
      dimensionMatrixPoint.{u, v} (finiteBijectionSum e f) := by
  change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
    (OrthogonalIndex.matrixPoint.{u, v} (finiteBijectionMatrix e) ⊗ₘ
      OrthogonalIndex.matrixPoint.{u, v} (finiteBijectionMatrix f)) ≫
      OrthogonalIndex.tensorMap.{u, v} m m n n = _
  exact (OrthogonalIndex.tensorMap_blockSum.{u, v}
    (finiteBijectionMatrix e) (finiteBijectionMatrix f)).1.trans
    (congrArg OrthogonalIndex.matrixPoint.{u, v} (finiteBijectionMatrix_blockSum e f))

theorem dimensionMatrixComposition {m n k : OrthogonalIndex}
    (e : Fin m ≃ Fin n) (f : Fin n ≃ Fin k) :
    dimensionMatrixPoint.{u, v} e ≫ dimensionMatrixPoint.{u, v} f =
      dimensionMatrixPoint.{u, v} (e.trans f) := by
  change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
    (OrthogonalIndex.matrixPoint.{u, v} (finiteBijectionMatrix e) ⊗ₘ
      OrthogonalIndex.matrixPoint.{u, v} (finiteBijectionMatrix f)) ≫
      @eComp PointedCGWH.{u, v} _ _ OrthogonalIndex
        (OrthogonalIndex.enrichedCategory.{u, v}) m n k = _
  exact (OrthogonalIndex.enrichedCategory_comp.{u, v}
    (finiteBijectionMatrix e) (finiteBijectionMatrix f)).1.trans
    (congrArg OrthogonalIndex.matrixPoint.{u, v} (finiteBijectionMatrix_comp e f))

private def dimensionCompatibility {m n : ℕ} (e : Fin m ≃ Fin n) : Prop :=
  (permutationIso (1 : OrthogonalIndex) e).hom ≫
      eqToHom (orthogonalDimensionPower.{v, u} n) =
    eqToHom (orthogonalDimensionPower.{v, u} m) ≫ dimensionMatrixPoint.{u, v} e

private theorem dimensionCompatibility_refl (n : ℕ) :
    dimensionCompatibility.{u, v} (Equiv.refl (Fin n)) := by
  dsimp only [dimensionCompatibility]
  rw [permutationIso_refl]
  have hM : dimensionMatrixPoint.{u, v} (Equiv.refl (Fin n)) = 𝟙 (n : OrthogonalIndex) := by
    change OrthogonalIndex.matrixPoint.{u, v} (finiteBijectionMatrix (Equiv.refl (Fin n))) = _
    rw [finiteBijectionMatrix_refl]
    exact (OrthogonalIndex.enrichedCategory_id.{u, v} n).symm
  rw [hM]
  simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

private theorem dimensionCompatibility_trans {m n k : ℕ}
    (e : Fin m ≃ Fin n) (f : Fin n ≃ Fin k)
    (he : dimensionCompatibility.{u, v} e) (hf : dimensionCompatibility.{u, v} f) :
    dimensionCompatibility.{u, v} (e.trans f) := by
  dsimp only [dimensionCompatibility] at he hf ⊢
  rw [permutationIso_trans]
  simp only [Iso.trans_hom, Category.assoc]
  rw [hf, ← Category.assoc, he, Category.assoc, dimensionMatrixComposition]

private theorem dimensionCompatibility_cast {m n : ℕ} (h : m = n) :
    dimensionCompatibility.{u, v} (finCongr h) := by
  subst n
  exact dimensionCompatibility_refl m

private theorem dimensionPoint_transport {m n p q : OrthogonalIndex}
    (hm : m = n) (hp : p = q) (e : Fin m ≃ Fin p) :
    eqToHom hm.symm ≫ dimensionMatrixPoint.{u, v} e ≫ eqToHom hp =
      dimensionMatrixPoint.{u, v} ((finCongr hm).symm.trans (e.trans (finCongr hp))) := by
  subst n
  subst q
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    finCongr_refl, Equiv.refl_symm, Equiv.refl_trans, Equiv.trans_refl]

private theorem dimensionCompatibility_block {m n : ℕ}
    (e : Equiv.Perm (Fin m)) (f : Equiv.Perm (Fin n))
    (he : dimensionCompatibility.{u, v} e) (hf : dimensionCompatibility.{u, v} f) :
    dimensionCompatibility.{u, v} (finiteBijectionSum e f) := by
  let b := finiteBijectionSum e f
  let add := tensorPowObj_add (1 : OrthogonalIndex) m n
  let dm := orthogonalDimensionPower.{v, u} m
  let dn := orthogonalDimensionPower.{v, u} n
  let ds := orthogonalDimensionPower.{v, u} (m + n)
  have hAdd : add.hom ≫ (eqToHom dm ⊗ₘ eqToHom dn) = eqToHom ds := by
    rw [orthogonalDimensionPower_addMap]
    have hCast : eqToHom dm ⊗ₘ eqToHom dn =
        eqToHom (congrArg₂ (fun a b : OrthogonalIndex => a + b) dm dn) := by
      rw [tensorHom_def, eqToHom_whiskerRight, whiskerLeft_eqToHom, eqToHom_trans]
    rw [hCast, eqToHom_trans]
  have hB : (permutationIso (1 : OrthogonalIndex) b).hom ≫ add.hom =
      add.hom ≫ ((permutationIso (1 : OrthogonalIndex) e).hom ⊗ₘ
        (permutationIso (1 : OrthogonalIndex) f).hom) := by
    have h := congrArg Iso.hom (blockSumIso_natural (1 : OrthogonalIndex) e f)
    have hh := congrArg (fun z => z ≫ add.hom) h.symm
    apply (cancel_epi add.inv).1
    simpa only [add, b, finiteBijectionSum, Iso.trans_hom, tensorIso_hom,
      Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using hh
  dsimp only [dimensionCompatibility] at he hf ⊢
  rw [← hAdd, ← Category.assoc, hB, Category.assoc,
    tensorHom_comp_tensorHom, he, hf, ← tensorHom_comp_tensorHom,
    ← Category.assoc, hAdd, dimensionMatrixTensor]

private theorem dimensionMatrixFlip (m n : OrthogonalIndex) :
    dimensionMatrixPoint.{u, v} (finAddFlip : Fin (m + n) ≃ Fin (n + m)) =
      (β_ m n).hom := by
  have hM : finiteBijectionMatrix (finAddFlip : Fin (m + n) ≃ Fin (n + m)) =
      OrthogonalIndex.blockSwap m n := finiteBijectionMatrix_blockSwap m n
  change OrthogonalIndex.matrixPoint.{u, v} _ = OrthogonalIndex.matrixPoint.{u, v} _
  exact congrArg OrthogonalIndex.matrixPoint.{u, v} hM

private theorem dimensionCompatibility_flip (m n : ℕ) :
    dimensionCompatibility.{u, v} (finAddFlip : Fin (m + n) ≃ Fin (n + m)) := by
  let pm := tensorPowObj (1 : OrthogonalIndex) m
  let pn := tensorPowObj (1 : OrthogonalIndex) n
  let dm := orthogonalDimensionPower.{v, u} m
  let dn := orthogonalDimensionPower.{v, u} n
  let ds := orthogonalDimensionPower.{v, u} (m + n)
  let ds' := orthogonalDimensionPower.{v, u} (n + m)
  let add := tensorPowObj_add (1 : OrthogonalIndex) m n
  let add' := tensorPowObj_add (1 : OrthogonalIndex) n m
  have hAdd : add.hom ≫ (eqToHom dm ⊗ₘ eqToHom dn) = eqToHom ds := by
    rw [orthogonalDimensionPower_addMap, tensorHom_def,
      eqToHom_whiskerRight, whiskerLeft_eqToHom, eqToHom_trans, eqToHom_trans]
  have hAdd' : add'.hom ≫ (eqToHom dn ⊗ₘ eqToHom dm) = eqToHom ds' := by
    rw [orthogonalDimensionPower_addMap, tensorHom_def,
      eqToHom_whiskerRight, whiskerLeft_eqToHom, eqToHom_trans, eqToHom_trans]
  have hB : (permutationIso (1 : OrthogonalIndex) finAddFlip).hom ≫ add'.hom =
      add.hom ≫ (β_ pm pn).hom := by
    have h := congrArg Iso.hom (blockSwap (1 : OrthogonalIndex) m n)
    have hh := congrArg (fun z => z ≫ add'.hom) h
    apply (cancel_epi add.inv).1
    simpa only [add, add', pm, pn, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using hh
  dsimp only [dimensionCompatibility]
  rw [← hAdd', ← Category.assoc, hB, Category.assoc,
    ← BraidedCategory.braiding_naturality (eqToHom dm) (eqToHom dn),
    ← Category.assoc, hAdd, dimensionMatrixFlip]

private theorem dimensionCompatibility_adjacent : ∀ n : ℕ, ∀ i : Fin n,
    dimensionCompatibility.{u, v} (Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (n + 1))) := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · let e := finAddFlip (m := 1) (n := 1)
        let b : Equiv.Perm (Fin (2 + n)) :=
          finSumFinEquiv.symm.trans
            ((Equiv.sumCongr e (Equiv.refl (Fin n))).trans finSumFinEquiv)
        let h : 2 + n = (n + 1) + 1 := by omega
        let p := (finCongr h).symm.trans (b.trans (finCongr h))
        have hb : dimensionCompatibility.{u, v} b := dimensionCompatibility_block.{u, v} e
          (Equiv.refl (Fin n)) (dimensionCompatibility_flip.{u, v} 1 1)
          (dimensionCompatibility_refl.{u, v} n)
        have hp : dimensionCompatibility.{u, v} p := dimensionCompatibility_trans.{u, v} _ _
          (dimensionCompatibility_cast.{u, v} h.symm)
          (dimensionCompatibility_trans.{u, v} b (finCongr h) hb
            (dimensionCompatibility_cast.{u, v} h))
        have ee : e = Equiv.swap (0 : Fin 2) (1 : Fin 2) := by
          apply Equiv.ext
          intro x
          fin_cases x <;> rfl
        have he : p = Equiv.swap (0 : Fin (n + 2)) (1 : Fin (n + 2)) := by
          dsimp only [p, b]
          rw [ee]
          change (finCongr h).symm.trans
            ((finSumFinEquiv.symm.trans
              ((Equiv.Perm.sumCongr (Equiv.swap (0 : Fin 2) (1 : Fin 2))
                (Equiv.refl (Fin n))).trans finSumFinEquiv)).trans (finCongr h)) = _
          rw [Equiv.Perm.sumCongr_swap_refl]
          have hbSwap := Equiv.symm_trans_swap_trans (Sum.inl (0 : Fin 2))
            (Sum.inl (1 : Fin 2)) (finSumFinEquiv : Fin 2 ⊕ Fin n ≃ Fin (2 + n))
          rw [Equiv.trans_assoc] at hbSwap
          rw [hbSwap]
          rw [← Equiv.trans_assoc, Equiv.symm_trans_swap_trans]
          congr 1
        have hExpected :
            (Equiv.swap (Fin.castSucc (0 : Fin (n + 1))) (Fin.succ (0 : Fin (n + 1))) :
              Equiv.Perm (Fin ((n + 1) + 1))) =
            Equiv.swap (0 : Fin (n + 2)) (1 : Fin (n + 2)) := rfl
        rw [hExpected, ← he]
        exact hp
      · let a := Equiv.swap j.castSucc j.succ
        let b : Equiv.Perm (Fin (1 + (n + 1))) :=
          finSumFinEquiv.symm.trans
            ((Equiv.sumCongr (Equiv.refl (Fin 1)) a).trans finSumFinEquiv)
        let h : 1 + (n + 1) = (n + 1) + 1 := by omega
        let p := (finCongr h).symm.trans (b.trans (finCongr h))
        have hb : dimensionCompatibility.{u, v} b := dimensionCompatibility_block.{u, v}
          (Equiv.refl (Fin 1)) a (dimensionCompatibility_refl.{u, v} 1) (ih j)
        have hp : dimensionCompatibility.{u, v} p := dimensionCompatibility_trans.{u, v} _ _
          (dimensionCompatibility_cast.{u, v} h.symm)
          (dimensionCompatibility_trans.{u, v} b (finCongr h) hb
            (dimensionCompatibility_cast.{u, v} h))
        have he : p = Equiv.swap j.succ.castSucc j.succ.succ := by
          dsimp only [p, b, a]
          change (finCongr h).symm.trans
            ((finSumFinEquiv.symm.trans
              ((Equiv.Perm.sumCongr (Equiv.refl (Fin 1))
                (Equiv.swap j.castSucc j.succ)).trans finSumFinEquiv)).trans (finCongr h)) = _
          rw [Equiv.Perm.sumCongr_refl_swap]
          have hbSwap := Equiv.symm_trans_swap_trans (Sum.inr j.castSucc)
            (Sum.inr j.succ) (finSumFinEquiv : Fin 1 ⊕ Fin (n + 1) ≃ Fin (1 + (n + 1)))
          rw [Equiv.trans_assoc] at hbSwap
          rw [hbSwap]
          rw [← Equiv.trans_assoc, Equiv.symm_trans_swap_trans]
          congr 1 <;> apply Fin.ext <;> simp
        rw [← he]
        exact hp


end CategoryTheory.Spectra

namespace CategoryTheory.Spectra

attribute [local instance] OrthogonalIndex.enrichedCategory OrthogonalIndex.category
  OrthogonalIndex.monoidalCategory OrthogonalIndex.enrichedOrdinaryCategory
  OrthogonalIndex.symmetricCategory

universe u v

/-- The original dimension tensor power realizes every permutation by its actual matrix point. -/
theorem originalDimensionPower_permutation {m n : ℕ} (e : Fin m ≃ Fin n) :
    (permutationIso (1 : OrthogonalIndex) e).hom ≫
      eqToHom (orthogonalDimensionPower.{v, u} n) =
    eqToHom (orthogonalDimensionPower.{v, u} m) ≫ dimensionMatrixPoint.{u, v} e := by
  have hmn : m = n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  change dimensionCompatibility.{u, v} e
  cases m with
  | zero =>
      have he : e = Equiv.refl (Fin 0) := Subsingleton.elim _ _
      rw [he]
      exact dimensionCompatibility_refl 0
  | succ n =>
      have he : e ∈ Submonoid.closure
          (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ]
        trivial
      apply Submonoid.closure_induction (motive := fun p _ => dimensionCompatibility.{u, v} p)
        (fun p hp => ?_) (dimensionCompatibility_refl (n + 1))
        (fun p q _ _ hp hq => dimensionCompatibility_trans q p hq hp) he
      obtain ⟨i, rfl⟩ := hp
      exact dimensionCompatibility_adjacent n i

end CategoryTheory.Spectra
