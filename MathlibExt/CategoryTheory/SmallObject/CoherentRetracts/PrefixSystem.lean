/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Codex
-/
module

public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Basic
public import Mathlib.Order.UpperLower.Closure
public import Mathlib.CategoryTheory.SmallObject.Iteration.Basic
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Complete original closed prefixes and their restriction system

A complete prefix retains its original splitting diagram, literal source
functor, identity bottom, actual successor pushout memberships and preceding
target colimit witnesses. Original inequalities construct full restrictions
with identity/composition laws; the actual identity seed and these maps give
the contravariant projective system.

The subsequent common gluing theorem accepts a compatible family. The final
coherent-retract induction constructs that family from this seed and genuine
successor and limit lifts. No completed family is an input or result here.

This is the original-prefix data used in Hovey, Model Categories,
Corollary 2.1.15 and the proof of Proposition 2.1.16, printed pp.33–34.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.SmallObject.CoherentRetracts

variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J]
  (P : MorphismProperty C) (F : J ⥤ C)

/-- A complete original-index prefix state, including both natural maps,
literal original source diagram, actual bottom, cellular successor maps
and the real preceding colimit condition at every original limit. -/
structure PrefixSplit (j : J) where
  /-- The complete splitting diagram on the original closed prefix. -/
  D : Set.Iic j ⥤ SplitObject C
  /-- The whole source functor is exactly the original restricted F. -/
  source_eq : D ⋙ SplitObject.sourceFunctor = (Set.initialSegIic j).monotone.functor ⋙ F
  /-- The original bottom point retains both identity splitting maps. -/
  bottom_eq : D.obj ⟨⊥, bot_le⟩ = SplitObject.identityObject (F.obj ⊥)
  /-- Every actual auxiliary successor is a pushout of the arbitrary original class. -/
  map_mem (i : J) (hi : i < j) :
    P.pushouts ((D.map (homOfLE (Order.le_succ i) :
      ⟨i, hi.le⟩ ⟶ ⟨Order.succ i, Order.succ_le_of_lt hi⟩)).right)
  /-- Every genuine original limit carries its actual preceding target colimit property. -/
  continuous (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
    Nonempty (IsColimit (SmallObject.coconeOfLE (D ⋙ SplitObject.targetFunctor) hij))

namespace PrefixSplit

variable {P F}

@[ext]
theorem ext {j : J} {S T : PrefixSplit P F j} (hD : S.D = T.D) : S = T := by
  cases S
  cases T
  cases hD
  rfl

/-- Restriction retains the entire original smaller prefix and both maps. -/
def restrict {j k : J} (S : PrefixSplit P F k) (h : j ≤ k) : PrefixSplit P F j where
  D := SmallObject.restrictionLE S.D h
  source_eq := by
    change (Set.initialSegIicIicOfLE h).monotone.functor ⋙ (S.D ⋙ SplitObject.sourceFunctor) = _
    rw [S.source_eq]
    rfl
  bottom_eq := S.bottom_eq
  map_mem i hi := S.map_mem i (lt_of_lt_of_le hi h)
  continuous i hi hij := S.continuous i hi (hij.trans h)

/-- Restricting at the same stage retains the exact full state. -/
theorem restrict_id {j : J} (S : PrefixSplit P F j) : S.restrict le_rfl = S := by
  apply ext
  rfl

/-- Restrictions retain exact original composition, not merely an isomorphism. -/
theorem restrict_comp {i j k : J} (S : PrefixSplit P F k) (hij : i ≤ j) (hjk : j ≤ k) :
    (S.restrict hjk).restrict hij = S.restrict (hij.trans hjk) := by
  apply ext
  rfl

/-- The genuine bottom prefix is the original diagram's identity splitting. -/
def seed : PrefixSplit P F (⊥ : J) where
  D := (Set.initialSegIic (⊥ : J)).monotone.functor ⋙ F ⋙ SplitObject.identityFunctor
  source_eq := rfl
  bottom_eq := rfl
  map_mem _i hi := (not_lt_bot hi).elim
  continuous i hi hij := by
    obtain rfl : i = ⊥ := le_antisymm hij bot_le
    exact (Order.not_isSuccLimit_bot hi).elim

end PrefixSplit

/-- The projective system consists of complete original prefix data.
Its successor and limit sections will be constructed, rather than assumed. -/
def prefixSplitFunctor : Jᵒᵖ ⥤ Type (max w u v) where
  obj j := PrefixSplit P F j.unop
  map f := ↾fun S ↦ S.restrict (leOfHom f.unop)
  map_id _j := by
    apply ConcreteCategory.hom_ext
    intro S
    exact S.restrict_id
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro S
    exact (S.restrict_comp (leOfHom g.unop) (leOfHom f.unop)).symm

end CategoryTheory.SmallObject.CoherentRetracts
