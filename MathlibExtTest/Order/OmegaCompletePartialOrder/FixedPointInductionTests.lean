/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Order.OmegaCompletePartialOrder.FixedPointInduction
public import MathlibExtTest.Order.OmegaCompletePartialOrder.ContinuousHomTests
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Algebra.Group.Nat.Even

/-!
# Tests for fixed-point induction

* Pins: the definition of `Admissible` and the statement of `lfp_induction`.
* `Part ℕ` is not a complete lattice: `some 0` and `some 1` have no least upper bound.
* Positive instances on domains that are not complete lattices: on `Part ℕ`, every value of the
  least fixed point of a constant map is even; on `ℕ → Part ℕ`, every value of the least fixed
  point of the factorial functional is positive.
* Negative control for closure under suprema: on `ℕ∞` with `f x = x + 1`, the predicate
  `x ≠ ⊤` holds at `⊥` and is preserved by `f`, but fails at `lfp f = ⊤`; it is not admissible.
* Negative control for the bottom clause: on `Part ℕ` with `f = id`, the predicate
  `x = some 4` is closed under suprema of chains and preserved by `f`, but fails at
  `lfp f = ⊥`.
-/

@[expose] public section

namespace OmegaCompletePartialOrder.ContinuousHom.FixedPointInductionTests

/-! ### Statement pins -/

/-- Pin: `Admissible` is exactly "holds at `⊥` and is closed under suprema of ω-chains". -/
theorem admissible_iff_pin {D : Type*} [OmegaCompletePartialOrder D] [OrderBot D]
    (P : D → Prop) : Admissible P ↔ P ⊥ ∧ ∀ c : Chain D, (∀ i, P (c i)) → P (ωSup c) :=
  Iff.rfl

/-- Pin: the statement of fixed-point induction. -/
theorem lfp_induction_pin : ∀ {D : Type*} [OmegaCompletePartialOrder D] [OrderBot D]
    (f : D →𝒄 D) {P : D → Prop}, Admissible P → (∀ x, P x → P (f x)) → P (lfp f) :=
  @lfp_induction

/-! ### `Part ℕ` is not a complete lattice -/

/-- The partial numbers `some 0` and `some 1` have no least upper bound in `Part ℕ`, so the
order of `Part ℕ` is not that of a complete lattice. -/
theorem part_nat_no_lub : ¬ ∃ s : Part ℕ, IsLUB {Part.some 0, Part.some 1} s := by
  rintro ⟨s, hs, -⟩
  have h0 : (0 : ℕ) ∈ s := hs (Set.mem_insert _ _) 0 (Part.mem_some 0)
  have h1 : (1 : ℕ) ∈ s := hs (Set.mem_insert_of_mem _ rfl) 1 (Part.mem_some 1)
  exact absurd (Part.mem_unique h0 h1) (by decide)

/-! ### Positive instance on `Part ℕ` -/

/-- Every value of a partial number is even. -/
def EvenValues (x : Part ℕ) : Prop := ∀ n ∈ x, Even n

/-- Having only even values is admissible on `Part ℕ`. -/
theorem evenValues_admissible : Admissible EvenValues := by
  refine ⟨fun n hn => absurd hn (Part.notMem_none n), fun c hc n hn => ?_⟩
  obtain ⟨i, hi⟩ := (Part.mem_ωSup n c).mp hn
  exact hc i n (hi ▸ Part.mem_some n)

/-- Every value of the least fixed point of the constant map `x ↦ some 4` is even, by
fixed-point induction. -/
theorem lfp_const_evenValues : EvenValues (lfp (const (Part.some 4) : Part ℕ →𝒄 Part ℕ)) :=
  lfp_induction _ evenValues_admissible fun _ _ _ hn => (Part.mem_some_iff.mp hn) ▸ ⟨2, rfl⟩

/-- The least fixed point of `x ↦ some 4` is defined, so the previous conclusion is not
vacuous. -/
theorem lfp_const_dom : (lfp (const (Part.some 4) : Part ℕ →𝒄 Part ℕ)).Dom := by
  rw [← lfp_eq]
  trivial

/-! ### Positive instance on `ℕ → Part ℕ` -/

/-- Every value of a partial function on the natural numbers is positive. -/
def PosValues (g : ℕ → Part ℕ) : Prop := ∀ n, ∀ v ∈ g n, 0 < v

/-- Having only positive values is admissible on `ℕ → Part ℕ`. -/
theorem posValues_admissible : Admissible PosValues := by
  refine ⟨fun n v hv => absurd hv (Part.notMem_none v), fun c hc n v hv => ?_⟩
  obtain ⟨i, hi⟩ := (Part.mem_ωSup v (c.map (Pi.evalOrderHom n))).mp hv
  exact hc i n v (by rw [show c i n = Part.some v from hi.symm]; exact Part.mem_some v)

/-- Every value of the least fixed point of the factorial functional is positive, by
fixed-point induction: the functional sends a partial function with positive values to one with
positive values. -/
theorem lfp_factF_pos : PosValues (lfp Tests.factF) := by
  refine lfp_induction _ posValues_admissible fun g hg n v hv => ?_
  by_cases hn : n = 0
  · simp [Tests.factF, hn] at hv
    omega
  · simp [Tests.factF, hn] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact Nat.mul_pos (hg _ w hw) (Nat.pos_of_ne_zero hn)

/-! ### Negative control: closure under suprema of chains is necessary -/

/-- The successor map on `ℕ∞` as a Scott-continuous map. -/
noncomputable def succENat : ℕ∞ →𝒄 ℕ∞ :=
  ofFun (· + 1) (ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h => add_le_add_left h 1, fun c => by
      change sSup (Set.range c) + 1 = sSup (Set.range fun i => c i + 1)
      rw [sSup_range, sSup_range, ENat.iSup_add]⟩)

/-- The least fixed point of the successor map on `ℕ∞` is `⊤`. -/
theorem lfp_succENat : lfp succENat = ⊤ := by
  have h : lfp succENat + 1 = lfp succENat := lfp_eq succENat
  induction h' : lfp succENat using ENat.recTopCoe with
  | top => rfl
  | coe n =>
      rw [h'] at h
      exact absurd (by exact_mod_cast h : n + 1 = n) (Nat.succ_ne_self n)

/-- The predicate `x ≠ ⊤` on `ℕ∞` holds at `⊥` and is preserved by the successor map, but fails
at its least fixed point, and it is not admissible: the chain of natural numbers has supremum
`⊤`. Fixed-point induction cannot drop closure under suprema of chains. -/
theorem lfp_induction_needs_ωSup_closure :
    (⊥ : ℕ∞) ≠ ⊤ ∧ (∀ x : ℕ∞, x ≠ ⊤ → succENat x ≠ ⊤) ∧ ¬ (lfp succENat ≠ ⊤) ∧
      ¬ Admissible (fun x : ℕ∞ => x ≠ ⊤) := by
  refine ⟨bot_ne_top, fun x hx => ?_, fun h => h lfp_succENat, fun hP => ?_⟩
  · change x + 1 ≠ ⊤
    simp [hx]
  · obtain ⟨-, hsup⟩ := hP
    let c : Chain ℕ∞ := ⟨⟨fun i => (i : ℕ∞), fun _ _ h => ENat.natCast_le_natCast.mpr h⟩⟩
    apply hsup c (fun i => ENat.natCast_ne_top i)
    change sSup (Set.range fun i : ℕ => (i : ℕ∞)) = ⊤
    rw [sSup_range, ENat.iSup_natCast]

/-! ### Negative control: the bottom clause is necessary -/

/-- The predicate `x = some 4` on `Part ℕ` is closed under suprema of chains and preserved by
the identity, but fails at the least fixed point `⊥` of the identity. Fixed-point induction
cannot drop the requirement `P ⊥`. -/
theorem lfp_induction_needs_bot :
    (∀ c : Chain (Part ℕ), (∀ i, c i = Part.some 4) → ωSup c = Part.some 4) ∧
      (∀ x : Part ℕ, x = Part.some 4 → (ContinuousHom.id : Part ℕ →𝒄 Part ℕ) x = Part.some 4) ∧
      lfp (ContinuousHom.id : Part ℕ →𝒄 Part ℕ) ≠ Part.some 4 := by
  refine ⟨fun c hc => Part.ωSup_eq_some ⟨0, (hc 0).symm⟩, fun x hx => hx, fun h => ?_⟩
  have hbot : lfp (ContinuousHom.id : Part ℕ →𝒄 Part ℕ) = ⊥ :=
    le_antisymm (lfp_le _ le_rfl) bot_le
  rw [hbot] at h
  exact Part.notMem_none 4 (h ▸ Part.mem_some 4)

end OmegaCompletePartialOrder.ContinuousHom.FixedPointInductionTests
