/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Connectedness and parity consequences of the source Y₅₅₅ presentation.
The recognition theorem is not assumed. See Basak, arXiv:0811.0062v2, §1.1.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Presentation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.WreathCentralizer

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The sixteen-vertex tree has no loops. -/
theorem y555Adjacent_irrefl (v : Y555Vertex) : ¬ y555Adjacent v v := by
  cases v with
  | none => simp [y555Adjacent]
  | some v => simp [y555Adjacent]

/-- The source diagram is undirected. -/
theorem y555Adjacent_symm (u v : Y555Vertex) :
    y555Adjacent u v ↔ y555Adjacent v u := by
  cases u <;> cases v <;> simp [y555Adjacent, eq_comm, or_comm, and_comm]

/-- Any invariant which agrees at the ends of every edge is constant.
This proves connectedness of the actual indexed tree without recognition. -/
theorem y555_edge_invariant {α : Type*} (f : Y555Vertex → α)
    (hf : ∀ u v, y555Adjacent u v → f u = f v) (v : Y555Vertex) :
    f v = f none := by
  cases v with
  | none => rfl
  | some v =>
    rcases v with ⟨arm, level⟩
    induction level using Fin.induction with
    | zero =>
      exact (hf none (some (arm, 0)) (by simp [y555Adjacent])).symm
    | succ i ih =>
      exact (hf (some (arm, i.succ)) (some (arm, i.castSucc))
        (by simp [y555Adjacent])).trans ih

/-- In C₂, an odd power of a product can be one only when its factors agree. -/
theorem wreathParity_mul_cube (x y : WreathParity) (h : (x * y) ^ 3 = 1) :
    x = y := by
  rcases wreathParity_cases x with rfl | rfl <;>
    rcases wreathParity_cases y with rfl | rfl
  · rfl
  · exact False.elim ((by decide : (1 * wreathFlip : WreathParity) ^ 3 ≠ 1) h)
  · exact False.elim ((by decide : (wreathFlip * 1 : WreathParity) ^ 3 ≠ 1) h)
  · rfl

/-- Every homomorphism to C₂ has the same value on all sixteen generators. -/
theorem y555_parity_generator (f : BimonsterPresentation →* WreathParity)
    (v : Y555Vertex) : f (PresentedGroup.of v) = f bimonsterSwap := by
  apply y555_edge_invariant (fun v => f (PresentedGroup.of v)) _ v
  intro u v huv
  apply wreathParity_mul_cube
  have hne : u ≠ v := by
    intro h
    subst v
    exact y555Adjacent_irrefl u huv
  have h := congrArg f (y555_coxeter_relation u v hne)
  simpa only [map_pow, map_mul, ite_eq_left huv, map_one] using h

/-- A homomorphism to C₂ killing the central vertex kills the whole group. -/
theorem y555_parity_trivial (f : BimonsterPresentation →* WreathParity)
    (hf : f bimonsterSwap = 1) : f = 1 := by
  apply PresentedGroup.ext
  intro v
  simpa only [MonoidHom.one_apply] using (y555_parity_generator f v).trans hf

/-- The nontrivial C₂ quotient is uniquely the source generator parity. -/
theorem y555_parity_eq (f : BimonsterPresentation →* WreathParity)
    (hf : f bimonsterSwap = wreathFlip) : f = bimonsterParity := by
  apply PresentedGroup.ext
  intro v
  rw [y555_parity_generator f v, hf, bimonsterParity_generator]
  rfl

/-- Surjectivity forces the central vertex into the nonzero C₂ coset. -/
theorem y555_surjective_parity_swap (f : BimonsterPresentation →* WreathParity)
    (hf : Function.Surjective f) : f bimonsterSwap = wreathFlip := by
  rcases wreathParity_cases (f bimonsterSwap) with h | h
  · obtain ⟨g, hg⟩ := hf wreathFlip
    rw [y555_parity_trivial f h, MonoidHom.one_apply] at hg
    exact False.elim ((by decide : (1 : WreathParity) ≠ wreathFlip) hg)
  · exact h

/-- Any surjection to an actual two-factor wreath product sends the central
vertex to an outer involution. -/
theorem y555_surjective_wreath_swap {M : Type*} [Group M]
    (f : BimonsterPresentation →* M ≀ᵣ WreathParity)
    (hf : Function.Surjective f) : (f bimonsterSwap).right = wreathFlip := by
  apply y555_surjective_parity_swap (RegularWreathProduct.rightHom.comp f)
  intro p
  obtain ⟨g, hg⟩ := hf (RegularWreathProduct.inl p)
  exact ⟨g, congrArg RegularWreathProduct.right hg⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
