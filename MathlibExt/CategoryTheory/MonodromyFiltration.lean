/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# The canonical kernel-image monodromy filtration

For an actual nilpotent endomorphism N with N^(b+1)=0, the step M_k is
the finite sum of ker(N^(i+1)) intersect im(N^j), for 0 <= i,j <= b and
i-j <= k. This fixes the filtration, rather than taking an arbitrary
filtration as an input. The diagram and graded quotients are actual
subobjects, inclusions and cokernels in the abelian category.

`MonodromyLaws` states the remaining finite-filtration, lowering and
graded-power laws. Every map in the power condition must factor the
actual N^r. There is no independently chosen isomorphism between grades.

Reference: Deligne, *La conjecture de Weil II*, section 1.6; Illusie,
*Autour du theoreme de monodromie locale*, section 1.5.
https://www.numdam.org/item/AST_1994__223__9_0/
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.CategoryTheory.MonodromyFiltration

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  {P : C} (N : End P) (b : ℕ)

/-- The actual finite kernel-image step, centered at zero. -/
def step (k : ℤ) : Subobject P :=
  (Finset.univ.filter (fun ij : Fin (b + 1) × Fin (b + 1) ↦
    (ij.1.val : ℤ) - ij.2.val ≤ k)).sup fun ij ↦
      kernelSubobject (N ^ (ij.1.val + 1)).asHom ⊓
        imageSubobject (N ^ ij.2.val).asHom

/-- Increasing the weight includes every preceding kernel-image summand. -/
theorem step_monotone : Monotone (step N b) := by
  intro k l hkl
  apply Finset.sup_mono
  intro ij hij
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
  exact hij.trans hkl

/-- The diagram of actual step objects and their prescribed inclusions. -/
def diagram : ℤ ⥤ C where
  obj k := (step N b k : C)
  map f := Subobject.ofLE _ _ (step_monotone N b (leOfHom f))
  map_id _k := Subobject.ofLE_refl _
  map_comp _f _g := (Subobject.ofLE_comp_ofLE _ _ _ _ _).symm

/-- The actual step inclusions into P. -/
def inclusion : diagram N b ⟶ (Functor.const ℤ).obj P where
  app k := (step N b k).arrow
  naturality k l f := by
    change Subobject.ofLE (step N b k) (step N b l)
        (step_monotone N b (leOfHom f)) ≫ (step N b l).arrow =
      (step N b k).arrow ≫ 𝟙 P
    rw [Category.comp_id]
    exact Subobject.ofLE_arrow (step_monotone N b (leOfHom f))

/-- The actual consecutive-step inclusion. -/
def previous (k : ℤ) : (step N b (k - 1) : C) ⟶ (step N b k : C) :=
  Subobject.ofLE _ _ (step_monotone N b (by omega))

/-- The actual graded piece M_k / M_(k-1). -/
abbrev grade (k : ℤ) : C := cokernel (previous N b k)

/-- The finite, lowering and actual induced-power laws of this canonical
filtration. The factors are pinned by the actual subobject arrows and N. -/
def MonodromyLaws : Prop :=
  (∃ lo hi : ℤ, (∀ k, k < lo → step N b k = ⊥) ∧
    ∀ k, hi < k → step N b k = ⊤) ∧
  (∀ k : ℤ, ∃ f : (step N b k : C) ⟶ (step N b (k - 2) : C),
    f ≫ (step N b (k - 2)).arrow = (step N b k).arrow ≫ N.asHom) ∧
  ∀ r : ℕ,
    ∃ f : (step N b (r : ℤ) : C) ⟶ (step N b (-(r : ℤ)) : C),
    ∃ g : (step N b ((r : ℤ) - 1) : C) ⟶
      (step N b (-(r : ℤ) - 1) : C),
      f ≫ (step N b (-(r : ℤ))).arrow =
          (step N b (r : ℤ)).arrow ≫ (N ^ r).asHom ∧
      g ≫ (step N b (-(r : ℤ) - 1)).arrow =
          (step N b ((r : ℤ) - 1)).arrow ≫ (N ^ r).asHom ∧
      ∃ h : previous N b (r : ℤ) ≫ f =
        g ≫ previous N b (-(r : ℤ)),
        IsIso (cokernel.map (previous N b (r : ℤ))
          (previous N b (-(r : ℤ))) g f h)

end MathlibExt.CategoryTheory.MonodromyFiltration
