/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import MathlibExt.CategoryTheory.SmallObject.SelectiveMapping

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w h a uJ vJ uC vC

open CategoryTheory CategoryTheory.Limits

namespace HomotopicalAlgebra.AttachCells

section NestedCofans

variable {C : Type uC} [Category.{vC} C]
  {S : Type w} {H : S → Type h} {A : ∀ s, H s → C}
  [∀ s, HasCoproduct (A s)]

/-- Flatten the given cofan while retaining its actual point and inner inclusions. -/
def flattenCofan (c : Cofan (fun s => ∐ A s)) :
    Cofan (fun p : Σ s, H s => A p.1 p.2) :=
  Cofan.mk c.pt (fun p => Sigma.ι (A p.1) p.2 ≫ c.inj p.1)

/-- Two nested universal coproducts give the displayed flattened cofan's universal property. -/
def flattenCofanIsColimit (c : Cofan (fun s => ∐ A s)) (hc : IsColimit c) :
    IsColimit (flattenCofan c) := by
  let desc (d : Cofan (fun p : Σ s, H s => A p.1 p.2)) : c.pt ⟶ d.pt :=
    Cofan.IsColimit.desc hc (fun s => Sigma.desc (fun h => d.inj ⟨s, h⟩))
  have fac (d : Cofan (fun p : Σ s, H s => A p.1 p.2)) (p : Σ s, H s) :
      (flattenCofan c).inj p ≫ desc d = d.inj p := by
    have ho : c.inj p.1 ≫ desc d = Sigma.desc (fun h => d.inj ⟨p.1, h⟩) :=
      Cofan.IsColimit.fac hc _ p.1
    have hi : Sigma.ι (A p.1) p.2 ≫ Sigma.desc (fun h => d.inj ⟨p.1, h⟩) =
        d.inj p := Sigma.ι_comp_desc _ p.2
    change (Sigma.ι (A p.1) p.2 ≫ c.inj p.1) ≫ desc d = _
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => Sigma.ι (A p.1) p.2 ≫ f) ho).trans hi)
  refine Cofan.IsColimit.mk _ desc fac ?_
  intro d m hm
  refine Cofan.IsColimit.hom_ext hc _ _ (fun s => ?_)
  apply Sigma.hom_ext
  intro h
  have h₁ : Sigma.ι (A s) h ≫ (c.inj s ≫ m) = d.inj ⟨s, h⟩ :=
    (Category.assoc _ _ _).symm.trans (hm ⟨s, h⟩)
  have h₂ : Sigma.ι (A s) h ≫ (c.inj s ≫ desc d) = d.inj ⟨s, h⟩ :=
    (Category.assoc _ _ _).symm.trans (fac d ⟨s, h⟩)
  exact h₁.trans h₂.symm

end NestedCofans

section FreeDiagrams

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]
  [∀ i j : J, HasCoproductsOfShape (i ⟶ j) C]
  {α : Type a} {A B : α → C} (g : ∀ t, A t ⟶ B t) (loc : α → J)
  {X Y : J ⥤ C} {f : X ⟶ Y}
  (c : AttachCells.{w} (fun t => (evaluationLeftAdjoint C (loc t)).map (g t)) f)
  (k : J)
  [PreservesColimit (Discrete.functor (fun s : c.ι =>
    (evaluationLeftAdjoint C (loc (c.π s))).obj (A (c.π s)))) ((evaluation J C).obj k)]
  [PreservesColimit (Discrete.functor (fun s : c.ι =>
    (evaluationLeftAdjoint C (loc (c.π s))).obj (B (c.π s)))) ((evaluation J C).obj k)]
  [PreservesColimit (span c.g₁ c.m) ((evaluation J C).obj k)]

/-- Evaluate the actual free-diagram attachment and flatten its ordinary Hom-indexed copowers. -/
def evaluateFreeDiagrams : AttachCells.{max w vJ} g (((evaluation J C).obj k).map f) := by
  let c' := c.mapOfPreserves ((evaluation J C).obj k)
  let a₁ : Cofan (fun s : c.ι => ∐ fun _ : loc (c.π s) ⟶ k => A (c.π s)) := c'.cofan₁
  let a₂ : Cofan (fun s : c.ι => ∐ fun _ : loc (c.π s) ⟶ k => B (c.π s)) := c'.cofan₂
  refine {
    ι := Σ s : c.ι, loc (c.π s) ⟶ k
    π := fun p => c.π p.1
    cofan₁ := flattenCofan a₁
    cofan₂ := flattenCofan a₂
    isColimit₁ := flattenCofanIsColimit a₁ c'.isColimit₁
    isColimit₂ := flattenCofanIsColimit a₂ c'.isColimit₂
    m := c'.m
    g₁ := c'.g₁
    g₂ := c'.g₂
    isPushout := c'.isPushout
    hm := ?_ }
  intro p
  let i₁ := Sigma.ι (fun _ : loc (c.π p.1) ⟶ k => A (c.π p.1)) p.2
  let i₂ := Sigma.ι (fun _ : loc (c.π p.1) ⟶ k => B (c.π p.1)) p.2
  let m := ((evaluation J C).obj k).map
    ((evaluationLeftAdjoint C (loc (c.π p.1))).map (g (c.π p.1)))
  have ho : c'.cofan₁.inj p.1 ≫ c'.m = m ≫ c'.cofan₂.inj p.1 := c'.hm p.1
  have hi : i₁ ≫ m = g (c.π p.1) ≫ i₂ := by
    change i₁ ≫ Sigma.desc (fun h => g (c.π p.1) ≫
      Sigma.ι (fun _ : loc (c.π p.1) ⟶ k => B (c.π p.1)) h) = _
    exact Sigma.ι_comp_desc _ p.2
  change (i₁ ≫ c'.cofan₁.inj p.1) ≫ c'.m =
    g (c.π p.1) ≫ (i₂ ≫ c'.cofan₂.inj p.1)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => i₁ ≫ q) ho).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ c'.cofan₂.inj p.1) hi).trans (Category.assoc _ _ _))))

/-- The actual flattened labels are pairs of an original cell and an ordinary index morphism. -/
theorem evaluateFreeDiagrams_index :
    (evaluateFreeDiagrams g loc c k).ι = (Σ s : c.ι, loc (c.π s) ⟶ k) := rfl

/-- Every source leg is the actual free summand followed by the original evaluated cofan leg. -/
theorem evaluateFreeDiagrams_source_generator (s : c.ι) (h : loc (c.π s) ⟶ k) :
    (evaluateFreeDiagrams g loc c k).cofan₁.inj ⟨s, h⟩ =
      Sigma.ι (fun _ : loc (c.π s) ⟶ k => A (c.π s)) h ≫ (c.cofan₁.inj s).app k := rfl

/-- Every target leg is the actual free summand followed by the original evaluated cofan leg. -/
theorem evaluateFreeDiagrams_target_generator (s : c.ι) (h : loc (c.π s) ⟶ k) :
    (evaluateFreeDiagrams g loc c k).cofan₂.inj ⟨s, h⟩ =
      Sigma.ι (fun _ : loc (c.π s) ⟶ k => B (c.π s)) h ≫ (c.cofan₂.inj s).app k := rfl

/-- Flattening retains the actual evaluated coproduct map. -/
theorem evaluateFreeDiagrams_map :
    (evaluateFreeDiagrams g loc c k).m = c.m.app k := rfl

/-- Shrink only the flattened cell labels, retaining the actual evaluated attachment square. -/
def evaluateFreeDiagramsOfSmall
    [Small.{w} (Σ s : c.ι, loc (c.π s) ⟶ k)] :
    AttachCells.{w} g (((evaluation J C).obj k).map f) :=
  (evaluateFreeDiagrams g loc c k).reindex
    (equivShrink (Σ s : c.ι, loc (c.π s) ⟶ k)).symm

end FreeDiagrams

end HomotopicalAlgebra.AttachCells
