/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Final
import MathlibExt.CategoryTheory.Filtered.NatTail

/-!
# The original free-diagram comparison for the natural-number tail

Restriction by n ↦ n+1 carries the actual Hom-coproduct free diagram at i
to the free diagram at i−1, including i=0 and i=1. Both comparison functions
keep each original coproduct injection. They are natural in every index
arrow and every coefficient map, giving the full free-generator Arrow Iso.
Projective cofibration preservation and the derived cofinal-tail comparison
are subsequent uses of this source construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe w u v
open CategoryTheory Limits
open CategoryTheory.Functor

namespace CategoryTheory.NatTail.FreeDiagrams

/-- Compatibility presentation of the canonical offset-one tail with the original n+1 objects. -/
abbrev tail : ℕ ⥤ ℕ where
  obj n := n + 1
  map {n m} f := eqToHom (Nat.one_add n).symm ≫ (NatTail.tailFunctor 1).map f ≫
    eqToHom (Nat.one_add m)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The complete original successor presentation is the canonical tail through its natural equality. -/
def tailIso : tail ≅ NatTail.tailFunctor 1 :=
  NatIso.ofComponents (fun n => eqToIso (Nat.one_add n).symm) (by
    intro n m f
    exact Subsingleton.elim _ _)

/-- Canonical offset-one finality supplies finality of the original transported tail. -/
instance tail_final : tail.Final := by
  let _ : (NatTail.tailFunctor 1).Final := NatTail.tailFunctor_final 1
  exact Functor.final_of_natIso tailIso.symm

/-- The exact original tail Hom is the predecessor free Hom, with all empty and endpoint cases. -/
def homEquiv (i n : ℕ) : (i ⟶ n + 1) ≃ (i - 1 ⟶ n) := by
  cases i with
  | zero =>
    exact
      { toFun := fun _ => homOfLE (Nat.zero_le n)
        invFun := fun _ => homOfLE (Nat.zero_le (n + 1))
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _ }
  | succ i =>
    exact
      { toFun := fun f => homOfLE (Nat.le_of_succ_le_succ (leOfHom f))
        invFun := fun f => homOfLE (Nat.succ_le_succ (leOfHom f))
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _ }

/-- The actual predecessor keeps every original order arrow, including its two zero endpoints. -/
def predecessor : ℕ ⥤ ℕ where
  obj n := n - 1
  map f := homOfLE (Nat.sub_le_sub_right (leOfHom f) 1)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The original order Hom comparison constructs the full predecessor/tail adjunction. -/
def predecessorTailAdjunction : predecessor ⊣ tail :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun i n => (homEquiv i n).symm
      homEquiv_naturality_left_symm := by intros; exact Subsingleton.elim _ _
      homEquiv_naturality_right := by intros; exact Subsingleton.elim _ _ }

/-- Tail restriction has the actual predecessor restriction as right adjoint on whole diagrams. -/
def restrictionAdjunction (C : Type u) [Category.{v} C] :
    (whiskeringLeft ℕ ℕ C).obj tail ⊣ (whiskeringLeft ℕ ℕ C).obj predecessor :=
  predecessorTailAdjunction.whiskerLeft C

/-- Every original nonadjacent index arrow preserves the complete Hom comparison. -/
theorem homEquiv_comp (i : ℕ) {n m : ℕ} (a : n ⟶ m) (f : i ⟶ n + 1) :
    homEquiv i m (f ≫ tail.map a) = homEquiv i n f ≫ a :=
  Subsingleton.elim _ _

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C]

local instance homCoproducts : ∀ a b : ℕ, HasCoproductsOfShape (a ⟶ b) C :=
  fun _ _ => inferInstance

private def constantCoproductIso {I J : Type} (e : I ≃ J) (A : C) :
    (∐ fun _ : I => A) ≅ (∐ fun _ : J => A) :=
  Sigma.reindex e (fun _ : J => A)

/-- The full component Iso is built from both actual families of coproduct injections. -/
def component (i n : ℕ) (A : C) :
    ((evaluationLeftAdjoint C i).obj A).obj (n + 1) ≅
      ((evaluationLeftAdjoint C (i - 1)).obj A).obj n :=
  constantCoproductIso (homEquiv i n) A

/-- The actual forward function keeps each original tail injection and its precise Hom label. -/
@[reassoc]
theorem component_hom_injection (i n : ℕ) (A : C) (f : i ⟶ n + 1) :
    Sigma.ι (fun _ : i ⟶ n + 1 => A) f ≫ (component i n A).hom =
      Sigma.ι (fun _ : i - 1 ⟶ n => A) (homEquiv i n f) := by
  exact Sigma.ι_reindex_hom (homEquiv i n) (fun _ : i - 1 ⟶ n => A) f

/-- Its inverse retains every actual predecessor injection and the inverse original Hom label. -/
theorem component_inv_injection (i n : ℕ) (A : C) (f : i - 1 ⟶ n) :
    Sigma.ι (fun _ : i - 1 ⟶ n => A) f ≫ (component i n A).inv =
      Sigma.ι (fun _ : i ⟶ n + 1 => A) ((homEquiv i n).symm f) := by
  have h := Sigma.ι_reindex_inv (homEquiv i n) (fun _ : i - 1 ⟶ n => A)
    ((homEquiv i n).symm f)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- The entire source component is natural on every original natural-number arrow. -/
theorem component_naturality (i : ℕ) (A : C) {n m : ℕ} (a : n ⟶ m) :
    ((evaluationLeftAdjoint C i).obj A).map (tail.map a) ≫ (component i m A).hom =
      (component i n A).hom ≫ ((evaluationLeftAdjoint C (i - 1)).obj A).map a := by
  let l := Sigma.desc (fun f : i ⟶ n + 1 =>
    Sigma.ι (fun _ : i ⟶ m + 1 => A) (f ≫ tail.map a))
  let r := Sigma.desc (fun f : i - 1 ⟶ n => Sigma.ι (fun _ : i - 1 ⟶ m => A) (f ≫ a))
  change l ≫ (component i m A).hom = (component i n A).hom ≫ r
  apply Sigma.hom_ext
  intro f
  have hl : Sigma.ι (fun _ : i ⟶ n + 1 => A) f ≫ l =
      Sigma.ι (fun _ : i ⟶ m + 1 => A) (f ≫ tail.map a) := by
    exact colimit.ι_desc _ _
  have hr : Sigma.ι (fun _ : i - 1 ⟶ n => A) (homEquiv i n f) ≫ r =
      Sigma.ι (fun _ : i - 1 ⟶ m => A) (homEquiv i n f ≫ a) := by
    exact colimit.ι_desc _ _
  calc
    _ = (Sigma.ι (fun _ : i ⟶ n + 1 => A) f ≫ l) ≫ (component i m A).hom :=
      (Category.assoc _ _ _).symm
    _ = Sigma.ι (fun _ : i ⟶ m + 1 => A) (f ≫ tail.map a) ≫ (component i m A).hom :=
      congrArg (· ≫ (component i m A).hom) hl
    _ = Sigma.ι (fun _ : i - 1 ⟶ m => A) (homEquiv i m (f ≫ tail.map a)) :=
      component_hom_injection i m A (f ≫ tail.map a)
    _ = Sigma.ι (fun _ : i - 1 ⟶ m => A) (homEquiv i n f ≫ a) :=
      congrArg (Sigma.ι (fun _ : i - 1 ⟶ m => A)) (homEquiv_comp i a f)
    _ = Sigma.ι (fun _ : i - 1 ⟶ n => A) (homEquiv i n f) ≫ r := hr.symm
    _ = (Sigma.ι (fun _ : i ⟶ n + 1 => A) f ≫ (component i n A).hom) ≫ r :=
      congrArg (· ≫ r) (component_hom_injection i n A f).symm
    _ = _ := Category.assoc _ _ _

/-- The actual free tail diagram has a full natural Iso to the original predecessor free diagram. -/
def diagramIso (i : ℕ) (A : C) :
    tail ⋙ (evaluationLeftAdjoint C i).obj A ≅ (evaluationLeftAdjoint C (i - 1)).obj A :=
  NatIso.ofComponents (fun n => component i n A) (fun a => component_naturality i A a)

/-- Every original coefficient arrow preserves the full free-tail comparison. -/
theorem component_coefficient (i n : ℕ) {A B : C} (a : A ⟶ B) :
    ((evaluationLeftAdjoint C i).map a).app (n + 1) ≫ (component i n B).hom =
      (component i n A).hom ≫ ((evaluationLeftAdjoint C (i - 1)).map a).app n := by
  let l := Sigma.desc (fun f : i ⟶ n + 1 => a ≫ Sigma.ι (fun _ : i ⟶ n + 1 => B) f)
  let r := Sigma.desc (fun f : i - 1 ⟶ n => a ≫ Sigma.ι (fun _ : i - 1 ⟶ n => B) f)
  change l ≫ (component i n B).hom = (component i n A).hom ≫ r
  apply Sigma.hom_ext
  intro f
  have hl : Sigma.ι (fun _ : i ⟶ n + 1 => A) f ≫ l =
      a ≫ Sigma.ι (fun _ : i ⟶ n + 1 => B) f := by
    exact colimit.ι_desc _ _
  have hr : Sigma.ι (fun _ : i - 1 ⟶ n => A) (homEquiv i n f) ≫ r =
      a ≫ Sigma.ι (fun _ : i - 1 ⟶ n => B) (homEquiv i n f) := by
    exact colimit.ι_desc _ _
  calc
    _ = (Sigma.ι (fun _ : i ⟶ n + 1 => A) f ≫ l) ≫ (component i n B).hom :=
      (Category.assoc _ _ _).symm
    _ = (a ≫ Sigma.ι (fun _ : i ⟶ n + 1 => B) f) ≫ (component i n B).hom :=
      congrArg (· ≫ (component i n B).hom) hl
    _ = a ≫ (Sigma.ι (fun _ : i ⟶ n + 1 => B) f ≫ (component i n B).hom) :=
      Category.assoc _ _ _
    _ = a ≫ Sigma.ι (fun _ : i - 1 ⟶ n => B) (homEquiv i n f) :=
      congrArg (a ≫ ·) (component_hom_injection i n B f)
    _ = Sigma.ι (fun _ : i - 1 ⟶ n => A) (homEquiv i n f) ≫ r := hr.symm
    _ = (Sigma.ι (fun _ : i ⟶ n + 1 => A) f ≫ (component i n A).hom) ≫ r :=
      congrArg (· ≫ r) (component_hom_injection i n A f).symm
    _ = _ := Category.assoc _ _ _

/-- The original free/evaluation functors retain all index and coefficient actions together. -/
def freeTailIso (i : ℕ) :
    evaluationLeftAdjoint C i ⋙ (whiskeringLeft ℕ ℕ C).obj tail ≅
      evaluationLeftAdjoint C (i - 1) :=
  NatIso.ofComponents (diagramIso i) (by
    intro A B a
    apply NatTrans.ext
    funext n
    exact component_coefficient i n a)

/-- The whole original free-generator Arrow is carried through both complete component Isos. -/
def freeArrowIso (i : ℕ) {A B : C} (a : A ⟶ B) :
    Arrow.mk (((whiskeringLeft ℕ ℕ C).obj tail).map ((evaluationLeftAdjoint C i).map a)) ≅
      Arrow.mk ((evaluationLeftAdjoint C (i - 1)).map a) :=
  Arrow.isoMk' _ _ ((freeTailIso i).app A) ((freeTailIso i).app B)
    ((freeTailIso i).hom.naturality a).symm

end CategoryTheory.NatTail.FreeDiagrams
