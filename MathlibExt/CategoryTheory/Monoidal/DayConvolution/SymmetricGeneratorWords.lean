/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.OrderedTensorWords
public import MathlibExt.CategoryTheory.Operad.FinBijDegreeInclusion
public import MathlibExt.CategoryTheory.Operad.FinBijTensorPower
public import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Symmetric generator words

A degree-one generator in a lax braided finite-bijection diagram extends
to a natural transformation from symmetric tensor powers. Every finite
bijection and block multiplication is respected.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor Limits MonoidalCategory
open scoped MonoidalCategory

namespace CategoryTheory.Operad.SmallFinBijGroupoid.SymmetricGeneratorWords
universe uV vV
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid
local notation "idx" => CategoryTheory.Sequence.index
attribute [local instance] degreeInclusionMonoidal

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  (F : I ⥤ V) [F.LaxBraided] {K : V} (g : K ⟶ F.obj (card 1))

/-- The actual complete ordered restriction of the original lax braided target diagram. -/
def orderedDiagram : CategoryTheory.Sequence.Index ⥤ V := degreeInclusion ⋙ F

/-- The original degree inclusion and target give the genuine ordered lax diagram. -/
@[instance_reducible]
def orderedLax : (orderedDiagram F).LaxMonoidal := Functor.LaxMonoidal.comp degreeInclusion F

attribute [local instance] orderedLax

/-- Every coefficient of the original symmetric-generator extension is its full ordered word. -/
def word (n : ℕ) : TensorPower.tensorPowObj K n ⟶ F.obj (card n) :=
  CategoryTheory.Sequence.OrderedTensorWords.word (orderedDiagram F) g n

/-- The entire ordered target multiplication is its original symmetric indexed multiplication. -/
theorem pairing_original (p q : ℕ) :
    Functor.LaxMonoidal.μ (orderedDiagram F) (idx p) (idx q) =
      Functor.LaxMonoidal.μ F (card p) (card q) := by
  let m : F.obj (card p) ⊗ F.obj (card q) ⟶ F.obj (card (p + q)) :=
    Functor.LaxMonoidal.μ F (card p) (card q)
  let r : F.obj (card (p + q)) ⟶ F.obj (card (p + q)) :=
    F.map (Functor.LaxMonoidal.μ degreeInclusion (idx p) (idx q))
  have hId : Functor.LaxMonoidal.μ degreeInclusion (idx p) (idx q) =
      𝟙 (card (p + q)) := rfl
  have hr : r = 𝟙 (F.obj (card (p + q))) :=
    (congrArg F.map hId).trans (F.map_id _)
  change m ≫ r = m
  exact (congrArg (fun t => m ≫ t) hr).trans (Category.comp_id m)

/-- Every pair of original word lengths preserves the whole symmetric indexed multiplication. -/
theorem word_multiplication (p q : ℕ) :
    (TensorPower.tensorPowObj_add K p q).inv ≫ word F g (p + q) =
      (word F g p ⊗ₘ word F g q) ≫
        Functor.LaxMonoidal.μ F (card p) (card q) :=
  (CategoryTheory.Sequence.OrderedTensorWords.word_multiplication (orderedDiagram F) g p q).symm.trans
    (congrArg (fun t => (word F g p ⊗ₘ word F g q) ≫ t) (pairing_original F p q))

/-- The whole original symmetric word extension retrieves the original degree-one generator. -/
theorem word_generator : (λ_ K).inv ≫ word F g 1 = g :=
  CategoryTheory.Sequence.OrderedTensorWords.word_one_generator (orderedDiagram F) g

end CategoryTheory.Operad.SmallFinBijGroupoid.SymmetricGeneratorWords


namespace CategoryTheory.Operad.SmallFinBijGroupoid.SymmetricGeneratorWords
universe uC vC
variable {C : Type uC} [Category.{vC} C]

/-- Five actual coefficient squares paste to the complete original outer square. -/
private theorem pasteCoefficientSquares {A B A' B' D E D' E' : C}
    (s : A ⟶ B) (r : A' ⟶ B') (t : D ⟶ E) (u : D' ⟶ E')
    (a : A ⟶ A') (b : B ⟶ B') (c : D ⟶ D') (d : E ⟶ E')
    (x : A ⟶ D) (y : B ⟶ E) (x' : A' ⟶ D') (y' : B' ⟶ E')
    (h₀ : s ≫ b = a ≫ r) (h₁ : r ≫ y' = x' ≫ u)
    (h₂ : a ≫ x' = x ≫ c) (h₃ : c ≫ u = t ≫ d) (h₄ : s ≫ y = x ≫ t) :
    s ≫ b ≫ y' = s ≫ y ≫ d :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ y') h₀).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => a ≫ f) h₁).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun f => f ≫ u) h₂).trans
              ((Category.assoc _ _ _).trans
                ((congrArg (fun f => x ≫ f) h₃).trans
                  ((Category.assoc _ _ _).symm.trans
                    ((congrArg (fun f => f ≫ d) h₄.symm).trans (Category.assoc _ _ _))))))))))

end CategoryTheory.Operad.SmallFinBijGroupoid.SymmetricGeneratorWords

namespace CategoryTheory.Operad.SmallFinBijGroupoid.SymmetricGeneratorWords
universe uV vV
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid
attribute [local instance] degreeInclusionMonoidal orderedLax
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  (F : I ⥤ V) [F.LaxBraided] {K : V} (g : K ⟶ F.obj (card 1))

/-- The original symmetric tensor-power coefficient functor. -/
def powers (K : V) : I ⥤ V := CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctor K

/-- The actual symmetric tensor-power functor keeps its original strong braided structure. -/
@[instance_reducible]
def powersBraided (K : V) : (powers K).Braided :=
  CategoryTheory.Operad.SmallFinBijGroupoid.tensorPowerFunctorBraided K

attribute [local instance] powersBraided

/-- Every original symmetric power tensorator is the same full ordered concatenation. -/
theorem powers_pairing (K : V) (p q : ℕ) :
    Functor.LaxMonoidal.μ (powers K) (card p) (card q) =
      (TensorPower.tensorPowObj_add K p q).inv := rfl

/-- Every original generator word respects the actual full symmetric coefficient pairing. -/
theorem word_pairing (p q : ℕ) :
    Functor.LaxMonoidal.μ (powers K) (card p) (card q) ≫ word F g (p + q) =
      (word F g p ⊗ₘ word F g q) ≫ Functor.LaxMonoidal.μ F (card p) (card q) :=
  (congrArg (fun t => t ≫ word F g (p + q)) (powers_pairing K p q)).trans
    (word_multiplication F g p q)

/-- The whole original word is natural for every original identity index arrow. -/
theorem word_identity (n : ℕ) :
    (powers K).map (𝟙 (card n)) ≫ word F g n =
      word F g n ≫ F.map (𝟙 (card n)) :=
  (congrArg (fun t => t ≫ word F g n) ((powers K).map_id _)).trans
    ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
      (congrArg (fun t => word F g n ≫ t) (F.map_id _).symm)))

/-- Tensoring any two complete original natural index arrows preserves every full generator word. -/
theorem word_tensor_natural (p q : ℕ)
    (f : card p ⟶ card p) (h : card q ⟶ card q)
    (hf : (powers K).map f ≫ word F g p = word F g p ≫ F.map f)
    (hh : (powers K).map h ≫ word F g q = word F g q ≫ F.map h) :
    (powers K).map (f ⊗ₘ h) ≫ word F g (p + q) =
      word F g (p + q) ≫ F.map (f ⊗ₘ h) := by
  let s : TensorPower.tensorPowObj K p ⊗ TensorPower.tensorPowObj K q ⟶
      TensorPower.tensorPowObj K (p + q) :=
    Functor.LaxMonoidal.μ (powers K) (card p) (card q)
  let t : F.obj (card p) ⊗ F.obj (card q) ⟶ F.obj (card (p + q)) :=
    Functor.LaxMonoidal.μ F (card p) (card q)
  let a := (powers K).map f ⊗ₘ (powers K).map h
  let b := (powers K).map (f ⊗ₘ h)
  let c := F.map f ⊗ₘ F.map h
  let d := F.map (f ⊗ₘ h)
  let x := word F g p ⊗ₘ word F g q
  let y := word F g (p + q)
  have hs : s ≫ b = a ≫ s := (Functor.LaxMonoidal.μ_natural (powers K) f h).symm
  have ht : c ≫ t = t ≫ d := Functor.LaxMonoidal.μ_natural F f h
  have hw : s ≫ y = x ≫ t := word_pairing F g p q
  have hx : a ≫ x = x ≫ c := by
    have h₀ := tensorHom_comp_tensorHom ((powers K).map f) ((powers K).map h)
      (word F g p) (word F g q)
    have h₁ := congrArg₂ (fun u v => u ⊗ₘ v) hf hh
    have h₂ := tensorHom_comp_tensorHom (word F g p) (word F g q) (F.map f) (F.map h)
    exact h₀.trans (h₁.trans h₂.symm)
  let _ : IsIso s := by
    change IsIso (TensorPower.tensorPowObj_add K p q).inv
    infer_instance
  exact (cancel_epi s).mp (pasteCoefficientSquares s s t t a b c d x y x y hs hw hx ht hw)

/-- Every original block braiding preserves the entire symmetric generator word. -/
theorem word_braiding_natural (p q : ℕ) :
    (powers K).map (β_ (card p) (card q)).hom ≫ word F g (q + p) =
      word F g (p + q) ≫ F.map (β_ (card p) (card q)).hom := by
  let s : TensorPower.tensorPowObj K p ⊗ TensorPower.tensorPowObj K q ⟶
      TensorPower.tensorPowObj K (p + q) :=
    Functor.LaxMonoidal.μ (powers K) (card p) (card q)
  let r : TensorPower.tensorPowObj K q ⊗ TensorPower.tensorPowObj K p ⟶
      TensorPower.tensorPowObj K (q + p) :=
    Functor.LaxMonoidal.μ (powers K) (card q) (card p)
  let t : F.obj (card p) ⊗ F.obj (card q) ⟶ F.obj (card (p + q)) :=
    Functor.LaxMonoidal.μ F (card p) (card q)
  let u : F.obj (card q) ⊗ F.obj (card p) ⟶ F.obj (card (q + p)) :=
    Functor.LaxMonoidal.μ F (card q) (card p)
  let a := (β_ (TensorPower.tensorPowObj K p) (TensorPower.tensorPowObj K q)).hom
  let b := (powers K).map (β_ (card p) (card q)).hom
  let c := (β_ (F.obj (card p)) (F.obj (card q))).hom
  let d := F.map (β_ (card p) (card q)).hom
  let x := word F g p ⊗ₘ word F g q
  let y := word F g (p + q)
  let x' := word F g q ⊗ₘ word F g p
  let y' := word F g (q + p)
  have hs : s ≫ b = a ≫ r :=
    Functor.LaxBraided.braided (F := powers K) (card p) (card q)
  have ht : c ≫ u = t ≫ d :=
    (Functor.LaxBraided.braided (F := F) (card p) (card q)).symm
  have hw : s ≫ y = x ≫ t := word_pairing F g p q
  have hw' : r ≫ y' = x' ≫ u := word_pairing F g q p
  have hx : a ≫ x' = x ≫ c := (BraidedCategory.braiding_naturality (word F g p) (word F g q)).symm
  let _ : IsIso s := by
    change IsIso (TensorPower.tensorPowObj_add K p q).inv
    infer_instance
  exact (cancel_epi s).mp (pasteCoefficientSquares s r t u a b c d x y x' y' hs hw' hx ht hw)

end CategoryTheory.Operad.SmallFinBijGroupoid.SymmetricGeneratorWords


namespace CategoryTheory.Operad.SmallFinBijGroupoid.FiniteCoefficientArrows

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- The entire original finite coordinate equivalence gives its genuine index isomorphism. -/
def iso {m n : ℕ} (e : Fin m ≃ Fin n) : card m ≅ card n :=
  mkCoreIso (Equiv.ulift.trans (e.trans Equiv.ulift.symm))

/-- The original finite index arrow keeps the whole supplied bijection. -/
def arrow {m n : ℕ} (e : Fin m ≃ Fin n) : card m ⟶ card n := (iso e).hom

/-- Every coordinate of this original index arrow is unchanged. -/
theorem coordinates {m n : ℕ} (e : Fin m ≃ Fin n) : smallEquivOfHom (arrow e) = e := by
  apply Equiv.ext
  intro z
  rfl

/-- The identity bijection retains the complete original identity index map. -/
theorem arrow_refl (n : ℕ) : arrow (Equiv.refl (Fin n)) = 𝟙 (card n) := by
  apply finiteArrow_ext
  have h : smallEquivOfHom (𝟙 (card n)) = Equiv.refl (Fin n) :=
    smallEquivOfHom_id (card n)
  exact (coordinates _).trans h.symm

/-- Composition retains the complete source-first original finite maps. -/
theorem arrow_trans {m n k : ℕ} (e : Fin m ≃ Fin n) (f : Fin n ≃ Fin k) :
    arrow (e.trans f) = arrow e ≫ arrow f := by
  apply finiteArrow_ext
  rw [coordinates, smallEquivOfHom_comp, coordinates, coordinates]
  rfl

/-- The original block sum keeps both whole original finite bijections. -/
theorem arrow_block {m n : ℕ} (e : Equiv.Perm (Fin m)) (f : Equiv.Perm (Fin n)) :
    arrow (finSumFinEquiv.symm.trans ((Equiv.sumCongr e f).trans finSumFinEquiv)) =
      arrow e ⊗ₘ arrow f := by
  apply finiteArrow_ext
  have h : smallEquivOfHom (arrow e ⊗ₘ arrow f) =
      finSumFinEquiv.symm.trans ((Equiv.sumCongr e f).trans finSumFinEquiv) :=
    (smallEquivOfHom_tensor (arrow e) (arrow f)).trans
      (congrArg₂ finiteBijectionSum (coordinates e) (coordinates f))
  exact (coordinates _).trans h.symm

/-- Every original block swap is the same actual finite index braiding. -/
theorem arrow_flip (m n : ℕ) :
    arrow (finAddFlip : Fin (m + n) ≃ Fin (n + m)) =
      (β_ (card m) (card n)).hom := by
  apply finiteArrow_ext
  have h : smallEquivOfHom (β_ (card m) (card n)).hom =
      (finAddFlip : Fin (m + n) ≃ Fin (n + m)) :=
    smallEquivOfHom_braiding (card m) (card n)
  exact (coordinates _).trans h.symm
end CategoryTheory.Operad.SmallFinBijGroupoid.FiniteCoefficientArrows

namespace CategoryTheory.Operad.SmallFinBijGroupoid.SymmetricGeneratorWords
universe uV vV
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid
attribute [local instance] degreeInclusionMonoidal orderedLax powersBraided
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  (F : I ⥤ V) [F.LaxBraided] {K : V} (g : K ⟶ F.obj (card 1))

/-- Naturality retains the complete original arrow on both sides of every word. -/
def compatibility {m n : ℕ} (e : Fin m ≃ Fin n) : Prop :=
  (powers K).map (FiniteCoefficientArrows.arrow e) ≫ word F g n =
    word F g m ≫ F.map (FiniteCoefficientArrows.arrow e)

/-- Every original identity coefficient is natural. -/
theorem compatibility_refl (n : ℕ) : compatibility F g (Equiv.refl (Fin n)) := by
  have h := FiniteCoefficientArrows.arrow_refl n
  exact (congrArg (fun t : card n ⟶ card n =>
    (powers K).map t ≫ word F g n) h).trans
      ((word_identity F g n).trans
        (congrArg (fun t : card n ⟶ card n => word F g n ≫ F.map t) h.symm))

/-- Two complete original coefficient naturalities compose. -/
theorem compatibility_trans {m n k : ℕ} (e : Fin m ≃ Fin n) (f : Fin n ≃ Fin k)
    (he : compatibility F g e) (hf : compatibility F g f) : compatibility F g (e.trans f) := by
  have hP : (powers K).map (FiniteCoefficientArrows.arrow (e.trans f)) =
      (powers K).map (FiniteCoefficientArrows.arrow e) ≫
        (powers K).map (FiniteCoefficientArrows.arrow f) :=
    (congrArg (powers K).map (FiniteCoefficientArrows.arrow_trans e f)).trans
      ((powers K).map_comp (FiniteCoefficientArrows.arrow e) (FiniteCoefficientArrows.arrow f))
  have hF : F.map (FiniteCoefficientArrows.arrow (e.trans f)) =
      F.map (FiniteCoefficientArrows.arrow e) ≫ F.map (FiniteCoefficientArrows.arrow f) :=
    (congrArg F.map (FiniteCoefficientArrows.arrow_trans e f)).trans
      (F.map_comp (FiniteCoefficientArrows.arrow e) (FiniteCoefficientArrows.arrow f))
  exact (congrArg (fun t : TensorPower.tensorPowObj K m ⟶ TensorPower.tensorPowObj K k =>
    t ≫ word F g k) hP).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => (powers K).map (FiniteCoefficientArrows.arrow e) ≫ t) hf).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun t => t ≫ F.map (FiniteCoefficientArrows.arrow f)) he).trans
              ((Category.assoc _ _ _).trans
                (congrArg (fun t : F.obj (card m) ⟶ F.obj (card k) =>
                  word F g m ≫ t) hF.symm))))))

/-- Both complete original block bijections preserve every full generator word. -/
theorem compatibility_block {m n : ℕ} (e : Equiv.Perm (Fin m)) (f : Equiv.Perm (Fin n))
    (he : compatibility F g e) (hf : compatibility F g f) :
    compatibility F g (finSumFinEquiv.symm.trans ((Equiv.sumCongr e f).trans finSumFinEquiv)) := by
  dsimp only [compatibility] at he hf ⊢
  rw [FiniteCoefficientArrows.arrow_block]
  exact word_tensor_natural F g m n (FiniteCoefficientArrows.arrow e)
    (FiniteCoefficientArrows.arrow f) he hf

/-- Every original block braiding preserves the complete word. -/
theorem compatibility_flip (m n : ℕ) :
    compatibility F g (finAddFlip : Fin (m + n) ≃ Fin (n + m)) := by
  dsimp only [compatibility]
  rw [FiniteCoefficientArrows.arrow_flip]
  exact word_braiding_natural F g m n

/-- Every actual equal-degree finite coordinate comparison preserves the complete word. -/
theorem compatibility_equal_degree {m n : ℕ} (h : m = n) : compatibility F g (finCongr h) := by
  subst n
  exact compatibility_refl F g m

private theorem compatibility_adjacent : ∀ n : ℕ, ∀ i : Fin n,
    compatibility F g (Equiv.swap i.castSucc i.succ : Equiv.Perm (Fin (n + 1))) := by
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
        have hb : compatibility F g b := compatibility_block F g e
          (Equiv.refl (Fin n)) (compatibility_flip F g 1 1) (compatibility_refl F g n)
        have hp : compatibility F g p := compatibility_trans F g _ _
          (compatibility_equal_degree F g h.symm)
          (compatibility_trans F g b (finCongr h) hb (compatibility_equal_degree F g h))
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
        have hb : compatibility F g b := compatibility_block F g
          (Equiv.refl (Fin 1)) a (compatibility_refl F g 1) (ih j)
        have hp : compatibility F g p := compatibility_trans F g _ _
          (compatibility_equal_degree F g h.symm)
          (compatibility_trans F g b (finCongr h) hb (compatibility_equal_degree F g h))
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

/-- Every original finite equivalence preserves the full original symmetric generator extension. -/
theorem word_permutation_natural {m n : ℕ} (e : Fin m ≃ Fin n) :
    compatibility F g e := by
  have hmn : m = n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  cases m with
  | zero =>
      have he : e = Equiv.refl (Fin 0) := Subsingleton.elim _ _
      rw [he]
      exact compatibility_refl F g 0
  | succ n =>
      have he : e ∈ Submonoid.closure
          (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ]
        trivial
      apply Submonoid.closure_induction (motive := fun p _ => compatibility F g p)
        (fun p hp => ?_) (compatibility_refl F g (n + 1))
        (fun p q _ _ hp hq => compatibility_trans F g q p hq hp) he
      obtain ⟨i, rfl⟩ := hp
      exact compatibility_adjacent F g n i

/-- Every whole original finite index arrow preserves the entire original generator word. -/
theorem word_natural {m n : ℕ} (f : card m ⟶ card n) :
    (powers K).map f ≫ word F g n = word F g m ≫ F.map f := by
  let e : Fin m ≃ Fin n := smallEquivOfHom f
  have h : (powers K).map (FiniteCoefficientArrows.arrow e) ≫ word F g n =
      word F g m ≫ F.map (FiniteCoefficientArrows.arrow e) :=
    word_permutation_natural F g (m := m) (n := n) e
  have hf : FiniteCoefficientArrows.arrow e = f := by
    apply finiteArrow_ext
    exact FiniteCoefficientArrows.coordinates e
  exact (congrArg (fun t : card m ⟶ card n =>
    (powers K).map t ≫ word F g n) hf.symm).trans
      (h.trans (congrArg (fun t : card m ⟶ card n => word F g m ≫ F.map t) hf))

/-- The complete original symmetric generator extension keeps every finite coefficient and map. -/
def fromGenerator : DayFunctor.mk (powers K) ⟶ DayFunctor.mk F where
  natTrans :=
    { app a := word F g a.of.len
      naturality := by
        rintro ⟨⟨m⟩⟩ ⟨⟨n⟩⟩ f
        exact word_natural F g f }

/-- Every original coefficient of the full extension is exactly its original word. -/
theorem fromGenerator_app (n : ℕ) :
    (fromGenerator F g).natTrans.app (card n) = word F g n := rfl

/-- The complete original symmetric extension recovers its entire degree-one generator. -/
theorem fromGenerator_generator :
    (λ_ K).inv ≫ (fromGenerator F g).natTrans.app (card 1) = g := word_generator F g

/-- The entire empty symmetric word is the original target unit coefficient. -/
theorem word_zero : word F g 0 = Functor.LaxMonoidal.ε F := by
  let r : F.obj (card 0) ⟶ F.obj (card 0) :=
    F.map (Functor.LaxMonoidal.ε degreeInclusion)
  have hi : Functor.LaxMonoidal.ε degreeInclusion = 𝟙 (card 0) := rfl
  have hr : r = 𝟙 (F.obj (card 0)) := (congrArg F.map hi).trans (F.map_id _)
  change Functor.LaxMonoidal.ε F ≫ r = Functor.LaxMonoidal.ε F
  exact (congrArg (fun t => Functor.LaxMonoidal.ε F ≫ t) hr).trans (Category.comp_id _)

/-- Every complete nonempty symmetric word uses its actual original target multiplication. -/
theorem word_successor (n : ℕ) :
    word F g (n + 1) = (word F g n ⊗ₘ g) ≫
      Functor.LaxMonoidal.μ F (card n) (card 1) :=
  (CategoryTheory.Sequence.OrderedTensorWords.word_successor (orderedDiagram F) g n).trans
    (congrArg (fun t => (word F g n ⊗ₘ g) ≫ t) (pairing_original F n 1))

end CategoryTheory.Operad.SmallFinBijGroupoid.SymmetricGeneratorWords
