/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The independent thirteen-generator Y444 Coxeter/spider presentation.
This is the literal nonterminal restriction of the original Y555 tree and spider10.
The source comparison is proved separately; no recognition is part of this definition. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555Parity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The central vertex and three independent four-vertex source arms. -/
abbrev Y444Vertex := Option (Fin 3 × Fin 4)

/-- Embed the exact thirteen nonterminal vertices in the original sixteen-vertex syntax. -/
def y444EmbedVertex (v : Y444Vertex) : Y555Vertex :=
  v.map fun p => (p.1, p.2.castSucc)

/-- The thirteen original source vertices have distinct embedded labels. -/
theorem y444EmbedVertex_injective : Function.Injective y444EmbedVertex := by decide +kernel

/-- Exact tree adjacency inherited from the original source syntax. -/
def y444Adjacent (u v : Y444Vertex) : Prop :=
  y555Adjacent (y444EmbedVertex u) (y444EmbedVertex v)

/-- Exact finite source adjacency is decidable. -/
instance y444AdjacentDecidable (u v : Y444Vertex) : Decidable (y444Adjacent u v) := by
  unfold y444Adjacent
  infer_instance

/-- The literal three-arm source spider, retaining the tenth-power exponent. -/
def y444Spider : FreeGroup Y444Vertex :=
  FreeGroup.of none * FreeGroup.of (some (0, 0)) * FreeGroup.of (some (0, 1)) *
    FreeGroup.of none * FreeGroup.of (some (1, 0)) * FreeGroup.of (some (1, 1)) *
      FreeGroup.of none * FreeGroup.of (some (2, 0)) * FreeGroup.of (some (2, 1))

/-- Independent squares, exact Coxeter pairs, and the original tenth spider power. -/
def y444Relations : Set (FreeGroup Y444Vertex) :=
  {w | (∃ v, w = FreeGroup.of v ^ 2) ∨
    (∃ u v, u ≠ v ∧ w = (FreeGroup.of u * FreeGroup.of v) ^
      (if y444Adjacent u v then 3 else 2 : ℕ)) ∨ w = y444Spider ^ 10}

/-- The independently presented thirteen-generator quotient. -/
abbrev Y444Presentation := PresentedGroup y444Relations

/-- Every original generator satisfies its defining square relation. -/
theorem y444_generator_sq (v : Y444Vertex) :
    (PresentedGroup.of v : Y444Presentation) ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := y444Relations)
    (show FreeGroup.of v ^ 2 ∈ y444Relations from Or.inl ⟨v, rfl⟩)
  simpa only [map_pow, PresentedGroup.of] using h

/-- Every exact source pair satisfies its defining Coxeter relation. -/
theorem y444_coxeter_relation (u v : Y444Vertex) (huv : u ≠ v) :
    ((PresentedGroup.of u : Y444Presentation) * PresentedGroup.of v) ^
      (if y444Adjacent u v then 3 else 2 : ℕ) = 1 := by
  have h := PresentedGroup.one_of_mem (rels := y444Relations)
    (show (FreeGroup.of u * FreeGroup.of v) ^
      (if y444Adjacent u v then 3 else 2 : ℕ) ∈ y444Relations from
        Or.inr (Or.inl ⟨u, v, huv, rfl⟩))
  simpa only [map_pow, map_mul, PresentedGroup.of] using h

/-- Every original thirteen-generator relator holds under the exact Y555 source inclusion. -/
theorem y444Relations_valid_Y555 (r : FreeGroup Y444Vertex) (hr : r ∈ y444Relations) :
    FreeGroup.lift (fun v =>
      (PresentedGroup.of (y444EmbedVertex v) : BimonsterPresentation)) r = 1 := by
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩ | rfl
  · simpa only [map_pow, FreeGroup.lift_apply_of] using
      y555_generator_sq (y444EmbedVertex v)
  · simpa only [map_pow, map_mul, FreeGroup.lift_apply_of, y444Adjacent] using
      y555_coxeter_relation (y444EmbedVertex u) (y444EmbedVertex v)
        (fun h => huv (y444EmbedVertex_injective h))
  · have h := PresentedGroup.one_of_mem (rels := y555Relations)
      (show y555Spider ^ 10 ∈ y555Relations from Or.inr (Or.inr rfl))
    simpa [y444Spider, y555Spider, y444EmbedVertex, map_pow, map_mul,
      FreeGroup.lift_apply_of, PresentedGroup.of, mul_assoc] using h

/-- The genuine original-source inclusion from the independent Y444 quotient to Y555. -/
def y444IntoY555 : Y444Presentation →* BimonsterPresentation :=
  PresentedGroup.toGroup y444Relations_valid_Y555

/-- Every embedded original generator retains its exact Y555 source value. -/
@[simp] theorem y444IntoY555_generator (v : Y444Vertex) :
    y444IntoY555 (PresentedGroup.of v) = PresentedGroup.of (y444EmbedVertex v) :=
  PresentedGroup.toGroup.of y444Relations_valid_Y555

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
