/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SymmetricTensorPower
public import MathlibExt.CategoryTheory.Monoidal.TensorPowerFunctor
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Strong braided functors preserve the original finite tensor permutations

The canonical comparison of the original left-associated tensor powers
intertwines every original finite-bijection action. The proof uses the
actual additive comparisons and block braiding, then finite generation by
adjacent transpositions, including the empty degree.
-/

public section

set_option autoImplicit false
noncomputable section

universe uC vC uD vD

open CategoryTheory MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open CategoryTheory.MonoidalCategory.SymmetricTensorPower

namespace CategoryTheory.MonoidalCategory.TensorPower.PermutationFunctorCompatibility

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D] [SymmetricCategory D]
  (G : C ⥤ D) [G.Braided] (X : C)

private def compatibility {m n : ℕ} (e : Fin m ≃ Fin n) : Prop :=
  G.map (permutationIso X e).hom ≫ (mapTensorPowObjIso G X n).hom =
    (mapTensorPowObjIso G X m).hom ≫ (permutationIso (G.obj X) e).hom

private theorem compatibility_refl (n : ℕ) :
    compatibility G X (Equiv.refl (Fin n)) := by
  simp [compatibility, permutationIso_refl]

private theorem compatibility_trans {m n k : ℕ}
    (e : Fin m ≃ Fin n) (f : Fin n ≃ Fin k)
    (he : compatibility G X e) (hf : compatibility G X f) :
    compatibility G X (e.trans f) := by
  dsimp only [compatibility] at he hf ⊢
  rw [permutationIso_trans, permutationIso_trans]
  simp only [Iso.trans_hom, G.map_comp, Category.assoc]
  rw [hf, ← Category.assoc, he, Category.assoc]

private theorem compatibility_block {m n : ℕ}
    (e : Equiv.Perm (Fin m)) (f : Equiv.Perm (Fin n))
    (he : compatibility G X e) (hf : compatibility G X f) :
    compatibility G X
      (finSumFinEquiv.symm.trans ((Equiv.sumCongr e f).trans finSumFinEquiv)) := by
  let block : Equiv.Perm (Fin (m + n)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr e f).trans finSumFinEquiv)
  let addC := tensorPowObj_add X m n
  let addD := tensorPowObj_add (G.obj X) m n
  let cm := (mapTensorPowObjIso G X m).hom
  let cn := (mapTensorPowObjIso G X n).hom
  let cs := (mapTensorPowObjIso G X (m + n)).hom
  let δ := Functor.OplaxMonoidal.δ G (tensorPowObj X m) (tensorPowObj X n)
  have hC : (permutationIso X block).hom ≫ addC.hom =
      addC.hom ≫ ((permutationIso X e).hom ⊗ₘ (permutationIso X f).hom) := by
    have h := congrArg Iso.hom (blockSumIso_natural X e f)
    apply (cancel_epi addC.inv).1
    have hh := congrArg (fun z => z ≫ addC.hom) h.symm
    simpa only [addC, block, Iso.trans_hom, tensorIso_hom, Category.assoc,
      Iso.symm_hom, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc] using hh
  have hD : (permutationIso (G.obj X) block).hom ≫ addD.hom =
      addD.hom ≫ ((permutationIso (G.obj X) e).hom ⊗ₘ
        (permutationIso (G.obj X) f).hom) := by
    have h := congrArg Iso.hom (blockSumIso_natural (G.obj X) e f)
    apply (cancel_epi addD.inv).1
    have hh := congrArg (fun z => z ≫ addD.hom) h.symm
    simpa only [addD, block, Iso.trans_hom, tensorIso_hom, Category.assoc,
      Iso.symm_hom, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc] using hh
  have hAdd : cs ≫ addD.hom = G.map addC.hom ≫ δ ≫ (cm ⊗ₘ cn) :=
    mapTensorPowObjIso_hom_add G X m n
  dsimp only [compatibility] at he hf ⊢
  change G.map (permutationIso X block).hom ≫ cs =
    cs ≫ (permutationIso (G.obj X) block).hom
  apply (cancel_mono addD.hom).1
  rw [Category.assoc, hAdd, ← G.map_comp_assoc, hC, G.map_comp]
  rw [Functor.Monoidal.map_tensor]
  simp only [Category.assoc]
  rw [Functor.Monoidal.μ_δ_assoc]
  rw [tensorHom_comp_tensorHom]
  change G.map addC.hom ≫ δ ≫
    ((G.map (permutationIso X e).hom ≫ cm) ⊗ₘ
      (G.map (permutationIso X f).hom ≫ cn)) = _
  rw [he, hf, ← tensorHom_comp_tensorHom]
  change G.map addC.hom ≫ δ ≫ (cm ⊗ₘ cn) ≫
    ((permutationIso (G.obj X) e).hom ⊗ₘ (permutationIso (G.obj X) f).hom) =
      cs ≫ (permutationIso (G.obj X) block).hom ≫ addD.hom
  have hh := congrArg (fun z => z ≫
    ((permutationIso (G.obj X) e).hom ⊗ₘ (permutationIso (G.obj X) f).hom)) hAdd.symm
  simpa only [Category.assoc, hD] using hh

private theorem compatibility_flip (m n : ℕ) :
    compatibility G X (finAddFlip : Fin (m + n) ≃ Fin (n + m)) := by
  let addC := tensorPowObj_add X m n
  let addC' := tensorPowObj_add X n m
  let addD := tensorPowObj_add (G.obj X) m n
  let addD' := tensorPowObj_add (G.obj X) n m
  let cm := (mapTensorPowObjIso G X m).hom
  let cn := (mapTensorPowObjIso G X n).hom
  let cs := (mapTensorPowObjIso G X (m + n)).hom
  let cs' := (mapTensorPowObjIso G X (n + m)).hom
  let δ := Functor.OplaxMonoidal.δ G (tensorPowObj X m) (tensorPowObj X n)
  have hC : (permutationIso X finAddFlip).hom ≫ addC'.hom =
      addC.hom ≫ (β_ (tensorPowObj X m) (tensorPowObj X n)).hom := by
    have h := congrArg Iso.hom (blockSwap X m n)
    have hh := congrArg (fun z => z ≫ addC'.hom) h
    apply (cancel_epi addC.inv).1
    simpa only [addC, addC', Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc] using hh
  have hD : (permutationIso (G.obj X) finAddFlip).hom ≫ addD'.hom =
      addD.hom ≫ (β_ (tensorPowObj (G.obj X) m) (tensorPowObj (G.obj X) n)).hom := by
    have h := congrArg Iso.hom (blockSwap (G.obj X) m n)
    have hh := congrArg (fun z => z ≫ addD'.hom) h
    apply (cancel_epi addD.inv).1
    simpa only [addD, addD', Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc] using hh
  have hAdd : cs ≫ addD.hom = G.map addC.hom ≫ δ ≫ (cm ⊗ₘ cn) :=
    mapTensorPowObjIso_hom_add G X m n
  have hAdd' : cs' ≫ addD'.hom = G.map addC'.hom ≫
      Functor.OplaxMonoidal.δ G (tensorPowObj X n) (tensorPowObj X m) ≫ (cn ⊗ₘ cm) :=
    mapTensorPowObjIso_hom_add G X n m
  dsimp only [compatibility]
  change G.map (permutationIso X finAddFlip).hom ≫ cs' =
    cs ≫ (permutationIso (G.obj X) finAddFlip).hom
  apply (cancel_mono addD'.hom).1
  rw [Category.assoc, hAdd', ← G.map_comp_assoc, hC, G.map_comp,
    G.map_braiding]
  simp only [Category.assoc]
  rw [Functor.Monoidal.μ_δ_assoc]
  rw [← BraidedCategory.braiding_naturality cm cn]
  change G.map addC.hom ≫ δ ≫ (cm ⊗ₘ cn) ≫
    (β_ (tensorPowObj (G.obj X) m) (tensorPowObj (G.obj X) n)).hom =
      cs ≫ (permutationIso (G.obj X) finAddFlip).hom ≫ addD'.hom
  have hh := congrArg (fun z => z ≫
    (β_ (tensorPowObj (G.obj X) m) (tensorPowObj (G.obj X) n)).hom) hAdd.symm
  simpa only [Category.assoc, hD] using hh

private theorem compatibility_cast {m n : ℕ} (h : m = n) :
    compatibility G X (finCongr h) := by
  subst n
  exact compatibility_refl G X m

private theorem compatibility_adjacent : ∀ n : ℕ, ∀ i : Fin n,
    compatibility G X (Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (n + 1))) := by
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
        have hb : compatibility G X b := compatibility_block G X e
          (Equiv.refl (Fin n)) (compatibility_flip G X 1 1) (compatibility_refl G X n)
        have hp : compatibility G X p := compatibility_trans G X _ _
          (compatibility_cast G X h.symm)
          (compatibility_trans G X b (finCongr h) hb (compatibility_cast G X h))
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
        have hb : compatibility G X b := compatibility_block G X
          (Equiv.refl (Fin 1)) a (compatibility_refl G X 1) (ih j)
        have hp : compatibility G X p := compatibility_trans G X _ _
          (compatibility_cast G X h.symm)
          (compatibility_trans G X b (finCongr h) hb (compatibility_cast G X h))
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

/-- The original strong braided comparison commutes with every finite permutation. -/
theorem mapTensorPowObjIso_permutation {m n : ℕ} (e : Fin m ≃ Fin n) :
    G.map (permutationIso X e).hom ≫ (mapTensorPowObjIso G X n).hom =
      (mapTensorPowObjIso G X m).hom ≫ (permutationIso (G.obj X) e).hom := by
  have hmn : m = n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  change compatibility G X e
  cases m with
  | zero =>
      have he : e = Equiv.refl (Fin 0) := Subsingleton.elim _ _
      rw [he]
      exact compatibility_refl G X 0
  | succ n =>
      have he : e ∈ Submonoid.closure
          (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ]
        trivial
      apply Submonoid.closure_induction (motive := fun p _ => compatibility G X p)
        (fun p hp => ?_) (compatibility_refl G X (n + 1))
        (fun p q _ _ hp hq => compatibility_trans G X q p hq hp) he
      obtain ⟨i, rfl⟩ := hp
      exact compatibility_adjacent G X n i

end CategoryTheory.MonoidalCategory.TensorPower.PermutationFunctorCompatibility
