/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialMittagLeffler
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Images of sequential limit projections

For a Mittag--Leffler inverse sequence, the image of every actual chosen-limit
projection is the native eventual range. The result applies to Type-valued
sequences and to concrete categories whose forgetful functor preserves the
given limit. No nonemptiness condition is added: membership of one eventual
range supplies the nonempty fibers needed to extend that element to a section.

These projection-image statements concern sequences indexed by `ℕᵒᵖ`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Set

universe u v w

namespace CategoryTheory.Functor

/-- A value in the eventual range of a Mittag--Leffler inverse sequence
extends to a compatible section with that exact coordinate. -/
theorem exists_section_of_mem_eventualRange
    (F : ℕᵒᵖ ⥤ Type w) (hF : F.IsMittagLeffler)
    {n : ℕ} {x : F.obj (op n)} (hx : x ∈ F.eventualRange (op n)) :
    ∃ s : F.sections, s.val (op n) = x := by
  let P := F.toPreimages ({x} : Set (F.obj (op n)))
  have hP : ∀ j : ℕᵒᵖ, Nonempty (P.obj j) := by
    intro j
    let m := max n j.unop
    let fn : op m ⟶ op n := (homOfLE (le_max_left n j.unop)).op
    let fj : op m ⟶ j := (homOfLE (le_max_right n j.unop)).op
    obtain ⟨y, hy⟩ := (F.mem_eventualRange_iff).mp hx fn
    refine ⟨⟨F.map fj y, ?_⟩⟩
    simp only [mem_iInter, mem_preimage, mem_singleton_iff]
    intro f
    have hcomp : fj ≫ f = fn := Subsingleton.elim _ _
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, hcomp]
    exact hy
  have : ∀ j : ℕᵒᵖ, Nonempty (P.obj j) := hP
  obtain ⟨s⟩ := P.nonempty_sections_of_isMittagLeffler
    (hF.toPreimages F ({x} : Set (F.obj (op n))))
  let t : F.sections :=
    ⟨fun j => (s.val j).val, fun f => by
      exact congrArg Subtype.val (s.property f)⟩
  refine ⟨t, ?_⟩
  have hs := (mem_iInter.mp (s.val (op n)).property) (𝟙 (op n))
  change F.map (𝟙 (op n)) (t.val (op n)) = x at hs
  rw [F.map_id] at hs
  exact hs

end CategoryTheory.Functor

namespace CategoryTheory.Limits.Types

/-- Every projection of the actual chosen limit of a Mittag--Leffler inverse
sequence has exactly its native eventual range as image. -/
theorem range_limit_π_eq_eventualRange_of_isMittagLeffler
    (F : ℕᵒᵖ ⥤ Type w) [HasLimit F] (hF : F.IsMittagLeffler) (n : ℕ) :
    range (limit.π F (op n)) = F.eventualRange (op n) := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, rfl⟩
    apply (F.mem_eventualRange_iff).mpr
    intro j f
    exact ⟨limit.π F j y, ConcreteCategory.congr_hom (limit.w F f) y⟩
  · intro x hx
    obtain ⟨s, hs⟩ := F.exists_section_of_mem_eventualRange hF hx
    refine ⟨(limitEquivSections F).symm s, ?_⟩
    exact (limitEquivSections_symm_apply F s (op n)).trans hs

end CategoryTheory.Limits.Types

namespace CategoryTheory.Limits.Concrete

variable {C : Type u} [Category.{v} C]
  {FC : C → C → Type*} {CC : C → Type w}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]

/-- In a concrete category preserving the given sequential limit, each actual
chosen-limit projection has the native eventual range as its underlying image. -/
theorem range_limit_π_eq_eventualRange_of_isMittagLeffler
    (F : ℕᵒᵖ ⥤ C) [HasLimit F] [PreservesLimit F (forget C)]
    (hF : F.IsSequentialMittagLeffler) (n : ℕ) :
    range ((forget C).map (limit.π F (op n))) =
      (F ⋙ forget C).eventualRange (op n) := by
  let U := F ⋙ forget C
  let e := preservesLimitIso (forget C) F
  apply Set.Subset.antisymm
  · rintro x ⟨y, rfl⟩
    have he : limit.π U (op n) (e.hom y) = (forget C).map (limit.π F (op n)) y :=
      ConcreteCategory.congr_hom (preservesLimitIso_hom_π (forget C) F (op n)) y
    have hmem := (Types.range_limit_π_eq_eventualRange_of_isMittagLeffler U hF n).le
      ⟨e.hom y, rfl⟩
    exact he ▸ hmem
  · intro x hx
    have hx' : x ∈ range (limit.π U (op n)) := by
      rw [Types.range_limit_π_eq_eventualRange_of_isMittagLeffler U hF n]
      exact hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨e.inv y, ?_⟩
    have he := ConcreteCategory.congr_hom
      (preservesLimitIso_inv_π (forget C) F (op n)) y
    exact he.trans hy

/-- Surjective successor transitions make every actual chosen-limit
projection surjective, provided forgetting preserves this sequential limit. -/
theorem surjective_limit_π_of_surjective_transition
    (F : ℕᵒᵖ ⥤ C) [HasLimit F] [PreservesLimit F (forget C)]
    (hF : ∀ n : ℕ, Function.Surjective
      (F.map (homOfLE (Nat.le_succ n)).op)) (n : ℕ) :
    Function.Surjective (limit.π F (op n)) := by
  let U := F ⋙ forget C
  have hU : ∀ ⦃i j : ℕᵒᵖ⦄ (f : i ⟶ j), Function.Surjective (U.map f) := by
    rintro ⟨i⟩ ⟨j⟩ f
    have hji : j ≤ i := leOfHom f.unop
    have hf : f = (homOfLE hji).op := Subsingleton.elim _ _
    rw [hf]
    exact U.surjective_map_of_eventually_surjective_transition
      (N := 0) (fun k _ => hF k) (Nat.zero_le j) hji
  have hML : F.IsSequentialMittagLeffler :=
    U.isMittagLeffler_of_surjective hU
  intro x
  have hx : x ∈ U.eventualRange (op n) := by
    apply (U.mem_eventualRange_iff).mpr
    intro i f
    exact hU f x
  exact (range_limit_π_eq_eventualRange_of_isMittagLeffler F hML n).ge hx

end CategoryTheory.Limits.Concrete
