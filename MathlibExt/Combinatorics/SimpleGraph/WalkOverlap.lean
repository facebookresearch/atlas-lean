/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source files at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_CerednikDrinfeld_WalkOverlap.lean`
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring

/-!
# Signed overlaps of walks

`CerednikDrinfeld.Mumford.walkOverlap P Q` counts, with signs, how often the walk `Q` traverses
the darts of the walk `P`: forward traversals count `+1` and backward traversals `-1`. It is
additive under concatenation in each argument, changes sign under reversal of either walk, and is
invariant under injective graph homomorphisms.
-/

@[expose] public section

namespace CerednikDrinfeld
namespace Mumford

variable {W : Type*} [DecidableEq W] {𝒯 : SimpleGraph W}

variable {α : Type*}

private theorem sum_map_neg_int (l : List α) (f : α → ℤ) :
    (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem sum_map_add_int (l : List α) (f g : α → ℤ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

omit [DecidableEq W] in
private theorem mapDart_injective {W' : Type*} {𝒯' : SimpleGraph W'} (f : 𝒯 →g 𝒯')
    (hf : Function.Injective f) :
    Function.Injective f.mapDart := by
  rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
  have h' := congrArg SimpleGraph.Dart.toProd h
  simp only [SimpleGraph.Hom.mapDart, Prod.map, Prod.mk.injEq] at h'
  obtain ⟨h1, h2⟩ := h'
  cases hf h1
  cases hf h2
  rfl

/-- The signed overlap of two walks: the sum over the darts `d` of `P` of the number of times `Q`
traverses `d` minus the number of times it traverses `d` reversed. -/
def walkOverlap {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') : ℤ :=
  (P.darts.map fun d => ((Q.darts.count d : ℕ) : ℤ) - ((Q.darts.count d.symm : ℕ) : ℤ)).sum

theorem walkOverlap_eq_sum {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    walkOverlap P Q =
        (P.darts.map fun d => ((Q.darts.count d : ℕ) : ℤ) - ((Q.darts.count d.symm : ℕ) : ℤ)).sum :=
  rfl

@[simp] theorem walkOverlap_nil_left (u : W) {u' v' : W} (Q : 𝒯.Walk u' v') :
    walkOverlap (SimpleGraph.Walk.nil : 𝒯.Walk u u) Q = 0 := by
  simp [walkOverlap]

@[simp] theorem walkOverlap_nil_right {u v : W} (P : 𝒯.Walk u v) (u' : W) :
    walkOverlap P (SimpleGraph.Walk.nil : 𝒯.Walk u' u') = 0 := by
  simp [walkOverlap]

theorem walkOverlap_cons_left {u v w u' v' : W} (h : 𝒯.Adj u v) (P : 𝒯.Walk v w)
    (Q : 𝒯.Walk u' v') :
    walkOverlap (SimpleGraph.Walk.cons h P) Q =
      (((Q.darts.count ⟨(u, v), h⟩ : ℕ) : ℤ) - ((Q.darts.count (⟨(u, v),
          h⟩ : 𝒯.Dart).symm : ℕ) : ℤ)) +
        walkOverlap P Q := by
  simp [walkOverlap]

/-- The overlap is additive in the first walk. -/
theorem walkOverlap_append_left {u v w u' v' : W} (P₁ : 𝒯.Walk u v) (P₂ : 𝒯.Walk v w)
    (Q : 𝒯.Walk u' v') :
    walkOverlap (P₁.append P₂) Q = walkOverlap P₁ Q + walkOverlap P₂ Q := by
  simp [walkOverlap, SimpleGraph.Walk.darts_append, List.sum_append]

/-- The overlap is additive in the second walk. -/
theorem walkOverlap_append_right {u v u' v' w' : W} (P : 𝒯.Walk u v) (Q₁ : 𝒯.Walk u' v')
    (Q₂ : 𝒯.Walk v' w') :
    walkOverlap P (Q₁.append Q₂) = walkOverlap P Q₁ + walkOverlap P Q₂ := by
  simp only [walkOverlap, SimpleGraph.Walk.darts_append, List.count_append, Nat.cast_add,
      ← sum_map_add_int]
  congr 1
  refine List.map_congr_left fun d _ => ?_
  ring

/-- Reversing the first walk negates the overlap. -/
theorem walkOverlap_reverse_left {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    walkOverlap P.reverse Q = -walkOverlap P Q := by
  simp only [walkOverlap, SimpleGraph.Walk.darts_reverse, List.map_reverse, List.sum_reverse,
      List.map_map,
    ← sum_map_neg_int]
  congr 1
  refine List.map_congr_left fun d _ => ?_
  simp only [Function.comp_apply, SimpleGraph.Dart.symm_symm]
  ring

/-- Reversing the second walk negates the overlap. -/
theorem walkOverlap_reverse_right {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    walkOverlap P Q.reverse = -walkOverlap P Q := by
  simp only [walkOverlap, SimpleGraph.Walk.darts_reverse, ← sum_map_neg_int]
  congr 1
  refine List.map_congr_left fun d _ => ?_
  have h1 : (Q.darts.map SimpleGraph.Dart.symm).reverse.count d = Q.darts.count d.symm := by
    rw [List.count_reverse, ← SimpleGraph.Dart.symm_symm d, List.count_map_of_injective _ _
      SimpleGraph.Dart.symm_involutive.injective, SimpleGraph.Dart.symm_symm]
  have h2 : (Q.darts.map SimpleGraph.Dart.symm).reverse.count d.symm = Q.darts.count d := by
    rw [List.count_reverse,
        List.count_map_of_injective _ _ SimpleGraph.Dart.symm_involutive.injective]
  rw [h1, h2]
  ring

/-- The overlap is invariant under injective graph homomorphisms. -/
theorem walkOverlap_map {W' : Type*} [DecidableEq W'] {𝒯' : SimpleGraph W'} (f : 𝒯 →g 𝒯')
    (hf : Function.Injective f) {u v u' v' : W} (P : 𝒯.Walk u v) (Q : 𝒯.Walk u' v') :
    walkOverlap (P.map f) (Q.map f) = walkOverlap P Q := by
  have hinj : Function.Injective f.mapDart := mapDart_injective f hf
  simp only [walkOverlap, SimpleGraph.Walk.darts_map, List.map_map]
  congr 1
  refine List.map_congr_left fun d _ => ?_
  simp only [Function.comp_apply]
  rw [List.count_map_of_injective _ _ hinj, show (f.mapDart d).symm = f.mapDart d.symm from rfl,
    List.count_map_of_injective _ _ hinj]

end Mumford
end CerednikDrinfeld
