/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.InfinitePi
public import MathlibExt.Probability.Configuration.ProductMeasure

/-!
# Independent branch choices at finite binary addresses

The sample space is one Bool choice per finite binary address
(`true` = branch, `false` = leaf), with independent Bernoulli(p)
choices at every address under `Measure.infinitePi`. Finite-address
cylinder probabilities are finite products, and prefix shifts reindex
to the subtree below a prefix.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Cslib.Language.BinaryTreeAddressLaw

/-! ## the coordinate law and the address law -/

/-- the sample space. One Bool choice per finite binary address:
`true` = branch, `false` = leaf. Abbreviation only; it is definitionally
`List Bool -> Bool` and introduces no tree or process structure. -/
abbrev Ω : Type :=
  List Bool → Bool

/-- Bernoulli(p) on one Bool coordinate: mass `p` on `true` (branch),
mass `1 - p` on `false` (leaf). This is the existing
`StatMech.bernoulliMeasure` at the nonnegative parameter corresponding
to `p`; the range proofs are part of the definition, so no measure is
exposed for invalid probabilities. -/
noncomputable def bernoulliBool (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure Bool :=
  StatMech.bernoulliMeasure (ENNReal.toNNReal (ENNReal.ofReal p))
    (by
      have hle : ENNReal.ofReal p ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hp1
      exact (ENNReal.toNNReal_le_toNNReal ENNReal.ofReal_ne_top ENNReal.one_ne_top).mpr hle)

/-- the independent branch-choice law on
`Ω = List Bool -> Bool`, defined directly as the existing Bernoulli
product measure `StatMech.bernoulliProductMeasure` at the nonnegative
parameter corresponding to `p`. The real parameter and its range proofs
are part of the definition, so no measure is exposed for invalid
probabilities; the grammar weight interface converts its real parameter
at this boundary. -/
noncomputable def law (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure Ω :=
  StatMech.bernoulliProductMeasure (E := List Bool)
    (ENNReal.toNNReal (ENNReal.ofReal p))
    (by
      have hle : ENNReal.ofReal p ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hp1
      exact (ENNReal.toNNReal_le_toNNReal ENNReal.ofReal_ne_top ENNReal.one_ne_top).mpr hle)

/-- bridge to Mathlib's unit-interval Bernoulli measure. -/
theorem bernoulliBool_eq_bernoulliMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bernoulliBool p hp0 hp1 = ProbabilityTheory.bernoulliMeasure true false ⟨p, hp0, hp1⟩ := by
  unfold bernoulliBool StatMech.bernoulliMeasure
  congr 1
  apply Subtype.ext
  show (ENNReal.ofReal p).toReal = p
  rw [ENNReal.toReal_ofReal hp0]

/-- The proof-indexed law is the constant-family `Measure.infinitePi` of
the coordinate law. -/
theorem law_eq_infinitePi {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    law p hp0 hp1 = Measure.infinitePi (fun _ : List Bool => bernoulliBool p hp0 hp1) := by
  unfold law StatMech.bernoulliProductMeasure bernoulliBool
  rfl

theorem bernoulliBool_isProbabilityMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliBool p hp0 hp1) := by
  rw [bernoulliBool_eq_bernoulliMeasure hp0 hp1]
  infer_instance

/-- coordinate masses. -/
theorem bernoulliBool_apply_true {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bernoulliBool p hp0 hp1 {true} = ENNReal.ofReal p := by
  unfold bernoulliBool
  rw [StatMech.bernoulliMeasure_apply_true]
  exact ENNReal.coe_toNNReal ENNReal.ofReal_ne_top

theorem bernoulliBool_apply_false {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bernoulliBool p hp0 hp1 {false} = ENNReal.ofReal (1 - p) := by
  have h0 : (0 : ℝ) ≤ 1 - p := by linarith
  rw [bernoulliBool_eq_bernoulliMeasure hp0 hp1,
    ProbabilityTheory.bernoulliMeasure_apply _ (measurableSet_singleton _)]
  simp only [Set.mem_singleton_iff, Bool.true_eq_false, ite_false, ite_true]
  exact (ENNReal.ofReal_eq_coe_nnreal h0).symm

theorem law_isProbabilityMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (law p hp0 hp1) := by
  haveI : ∀ _ : List Bool, IsProbabilityMeasure (bernoulliBool p hp0 hp1) :=
    fun _ => bernoulliBool_isProbabilityMeasure hp0 hp1
  rw [law_eq_infinitePi hp0 hp1]
  infer_instance

/-- each address coordinate of `law p hp0 hp1` is `bernoulliBool p hp0 hp1`
(`Measure.infinitePi_map_eval` at the constant family). -/
theorem law_map_eval {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a : List Bool) :
    (law p hp0 hp1).map (fun ω : Ω => ω a) = bernoulliBool p hp0 hp1 := by
  have hInst : ∀ i : List Bool, IsProbabilityMeasure ((fun _ : List Bool => bernoulliBool p hp0 hp1) i) :=
    fun _ => bernoulliBool_isProbabilityMeasure hp0 hp1
  rw [law_eq_infinitePi hp0 hp1]
  exact @Measure.infinitePi_map_eval (List Bool) (fun _ => Bool) _ (fun _ => bernoulliBool p hp0 hp1) hInst a

/-- On the probability range, this law is the existing Bernoulli product
measure `StatMech.bernoulliProductMeasure` at the corresponding
nonnegative parameter. The real-parameter form is retained because the
grammar weight interface below it is real-valued. -/
theorem law_eq_bernoulliProductMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    law p hp0 hp1 = StatMech.bernoulliProductMeasure (E := List Bool)
      (ENNReal.toNNReal (ENNReal.ofReal p))
      (by
        have hle : ENNReal.ofReal p ≤ 1 := by simpa using ENNReal.ofReal_le_ofReal hp1
        exact (ENNReal.toNNReal_le_toNNReal ENNReal.ofReal_ne_top ENNReal.one_ne_top).mpr hle) := by
  rfl

/-! ## finite-address cylinders and their masses -/

/-- the finite-address cylinder fixing the choices on the finset
`s` to the assignment `t`, leaving every address outside `s` (in
particular every descendant of a leaf in `s`) unrestricted. This is a
plain finite-coordinate event, not a tree type. -/
def cylinder (s : Finset (List Bool)) (t : List Bool → Bool) : Set Ω :=
  {ω : Ω | ∀ a ∈ s, ω a = t a}

/-- the product mass of
`cylinder s t` under `law p hp0 hp1`: one factor `p` per address assigned
`true` (branch) and one factor `1 - p` per address assigned `false`
(leaf). -/
noncomputable def cylinder_mass (p : ℝ) (s : Finset (List Bool)) (t : List Bool → Bool) :
    ℝ≥0∞ :=
  ∏ a ∈ s, (if t a then ENNReal.ofReal p else ENNReal.ofReal (1 - p))

theorem mem_cylinder {s : Finset (List Bool)} {t : List Bool → Bool} {ω : Ω} :
    ω ∈ cylinder s t ↔ ∀ a ∈ s, ω a = t a := by
  rfl

/-- the finite-product formula for `law p hp0 hp1`, directly
`Measure.infinitePi_pi` at the constant family. -/
theorem law_pi {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Finset (List Bool))
    (T : List Bool → Set Bool) (hT : ∀ a ∈ s, MeasurableSet (T a)) :
    law p hp0 hp1 ((s : Set (List Bool)).pi T) = ∏ a ∈ s, bernoulliBool p hp0 hp1 (T a) := by
  have hInst : ∀ i : List Bool, IsProbabilityMeasure ((fun _ : List Bool => bernoulliBool p hp0 hp1) i) :=
    fun _ => bernoulliBool_isProbabilityMeasure hp0 hp1
  rw [law_eq_infinitePi hp0 hp1]
  exact @Measure.infinitePi_pi (List Bool) (fun _ => Bool) _ (fun _ => bernoulliBool p hp0 hp1) hInst s T hT

/-- the same formula in Mathlib's `MeasureTheory.cylinder` form,
directly `Measure.infinitePi_cylinder` at the constant family. -/
theorem law_mathlib_cylinder {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Finset (List Bool)) {S : Set (∀ _ : s, Bool)} (hS : MeasurableSet S) :
    law p hp0 hp1 (MeasureTheory.cylinder s S) =
      Measure.pi (fun _ : s => bernoulliBool p hp0 hp1) S := by
  have hInst : ∀ i : List Bool, IsProbabilityMeasure ((fun _ : List Bool => bernoulliBool p hp0 hp1) i) :=
    fun _ => bernoulliBool_isProbabilityMeasure hp0 hp1
  rw [law_eq_infinitePi hp0 hp1]
  exact @Measure.infinitePi_cylinder (List Bool) (fun _ => Bool) _ (fun _ => bernoulliBool p hp0 hp1) hInst s S hS

/-- the headline cylinder probability. -/
theorem law_cylinder {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Finset (List Bool)) (t : List Bool → Bool) :
    law p hp0 hp1 (cylinder s t) = cylinder_mass p s t := by
  have hcyl : cylinder s t = (s : Set (List Bool)).pi (fun a => ({t a} : Set Bool)) := by
    ext ω
    simp [cylinder, Set.pi, Set.mem_singleton_iff]
  rw [hcyl, law_pi hp0 hp1 s _ (fun a _ => measurableSet_singleton _)]
  unfold cylinder_mass
  apply Finset.prod_congr rfl
  intro a _
  cases t a
  · simp [bernoulliBool_apply_false]
  · simp [bernoulliBool_apply_true]

/-- `cylinder_mass` is the product of the coordinate singleton
masses, the bridge between the two formulas above. -/
theorem cylinder_mass_eq_prod {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Finset (List Bool)) (t : List Bool → Bool) :
    cylinder_mass p s t = ∏ a ∈ s, bernoulliBool p hp0 hp1 {t a} := by
  unfold cylinder_mass
  apply Finset.prod_congr rfl
  intro a _
  cases t a
  · simp [bernoulliBool_apply_false]
  · simp [bernoulliBool_apply_true]

theorem cylinder_empty (t : List Bool → Bool) :
    cylinder ∅ t = Set.univ := by
  ext ω
  simp [cylinder]

theorem law_cylinder_empty {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : List Bool → Bool) :
    law p hp0 hp1 (cylinder ∅ t) = 1 := by
  have h : IsProbabilityMeasure (law p hp0 hp1) := law_isProbabilityMeasure hp0 hp1
  rw [cylinder_empty, @measure_univ Ω _ (law p hp0 hp1) h]

theorem cylinder_mass_insert {p : ℝ} {a : List Bool} {s : Finset (List Bool)}
    (ha : a ∉ s) (t : List Bool → Bool) :
    cylinder_mass p (insert a s) t =
      (if t a then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) * cylinder_mass p s t := by
  simp [cylinder_mass, Finset.prod_insert ha]

theorem cylinder_mass_singleton {p : ℝ} (a : List Bool) (t : List Bool → Bool) :
    cylinder_mass p {a} t =
      (if t a then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) := by
  simp [cylinder_mass]

/-! ## root choice, left/right cylinders, boundary probabilities -/

/-- the event that the node at address `a` branches. -/
def branchAt (a : List Bool) : Set Ω :=
  {ω : Ω | ω a = true}

/-- the event that the node at address `a` is a leaf. -/
def leafAt (a : List Bool) : Set Ω :=
  {ω : Ω | ω a = false}

theorem measurableSet_cylinder (s : Finset (List Bool)) (t : List Bool → Bool) :
    MeasurableSet (cylinder s t) := by
  have h : cylinder s t = ⋂ a ∈ s, {ω : Ω | ω a = t a} := by
    ext ω
    simp [cylinder]
  rw [h]
  exact MeasurableSet.biInter (Finset.countable_toSet s) (fun a _ =>
    measurableSet_eq_fun (measurable_pi_apply a) measurable_const)

theorem measurableSet_branchAt (a : List Bool) : MeasurableSet (branchAt a) := by
  rw [show branchAt a = cylinder {a} (fun _ => true) from by
    ext ω
    simp [branchAt, cylinder]]
  exact measurableSet_cylinder {a} (fun _ => true)

theorem measurableSet_leafAt (a : List Bool) : MeasurableSet (leafAt a) := by
  rw [show leafAt a = cylinder {a} (fun _ => false) from by
    ext ω
    simp [leafAt, cylinder]]
  exact measurableSet_cylinder {a} (fun _ => false)

theorem branchAt_eq_cylinder (a : List Bool) :
    branchAt a = cylinder {a} (fun _ => true) := by
  ext ω
  simp [branchAt, cylinder]

theorem leafAt_eq_cylinder (a : List Bool) :
    leafAt a = cylinder {a} (fun _ => false) := by
  ext ω
  simp [leafAt, cylinder]

/-- (nonvacuity, root choice): the root branches with mass `p`. -/
theorem law_root_branch {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    law p hp0 hp1 (branchAt []) = ENNReal.ofReal p := by
  rw [branchAt_eq_cylinder, law_cylinder hp0 hp1, cylinder_mass_singleton]
  simp

/-- (nonvacuity, root choice): the root is a leaf with mass `1 - p`. -/
theorem law_root_leaf {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    law p hp0 hp1 (leafAt []) = ENNReal.ofReal (1 - p) := by
  rw [leafAt_eq_cylinder, law_cylinder hp0 hp1, cylinder_mass_singleton]
  simp

/-- two cylinders on the same finset that disagree at one address
are disjoint. -/
theorem cylinder_disjoint_of_ne {s : Finset (List Bool)} {t₁ t₂ : List Bool → Bool}
    {a : List Bool} (ha : a ∈ s) (h : t₁ a ≠ t₂ a) :
    Disjoint (cylinder s t₁) (cylinder s t₂) := by
  rw [Set.disjoint_left]
  intro ω h1 h2
  simp [cylinder] at h1 h2
  have h1a := h1 a ha
  have h2a := h2 a ha
  exact h (h1a.symm.trans h2a)

/-- branch and leaf events at one address are disjoint. -/
theorem branchAt_disjoint_leafAt (a : List Bool) :
    Disjoint (branchAt a) (leafAt a) := by
  rw [Set.disjoint_left]
  intro ω h1 h2
  simp [branchAt, leafAt] at h1 h2
  rw [h1] at h2
  simp at h2

/-- (nonvacuity, disjoint left cylinders): the two choices at the
left-child address `[false]` are disjoint. -/
theorem disjoint_left_cylinders :
    Disjoint (cylinder {[false]} (fun _ => true)) (cylinder {[false]} (fun _ => false)) := by
  exact cylinder_disjoint_of_ne (Finset.mem_singleton_self _) (by simp)

/-- (nonvacuity, disjoint right cylinders): the two choices at the
right-child address `[true]` are disjoint. -/
theorem disjoint_right_cylinders :
    Disjoint (cylinder {[true]} (fun _ => true)) (cylinder {[true]} (fun _ => false)) := by
  exact cylinder_disjoint_of_ne (Finset.mem_singleton_self _) (by simp)

/-- (boundary coordinate laws). -/
theorem bernoulliBool_zero :
    bernoulliBool 0 le_rfl zero_le_one = Measure.dirac false := by
  rw [bernoulliBool_eq_bernoulliMeasure]
  rw [show (⟨0, le_rfl, zero_le_one⟩ : unitInterval) = 0 from Subtype.ext rfl]
  simp [ProbabilityTheory.bernoulliMeasure]

theorem bernoulliBool_one :
    bernoulliBool 1 zero_le_one le_rfl = Measure.dirac true := by
  rw [bernoulliBool_eq_bernoulliMeasure]
  rw [show (⟨1, zero_le_one, le_rfl⟩ : unitInterval) = 1 from Subtype.ext rfl]
  simp [ProbabilityTheory.bernoulliMeasure]

/-- (boundary `p = 0`): the root is almost surely a leaf. -/
theorem law_zero_root :
    law 0 le_rfl zero_le_one (leafAt []) = 1 ∧ law 0 le_rfl zero_le_one (branchAt []) = 0 := by
  have hleaf := law_root_leaf (show (0 : ℝ) ≤ 0 from le_rfl) (show (0 : ℝ) ≤ 1 from zero_le_one)
  have hbranch := law_root_branch (show (0 : ℝ) ≤ 0 from le_rfl) (show (0 : ℝ) ≤ 1 from zero_le_one)
  constructor
  · rw [hleaf]
    norm_num
  · rw [hbranch]
    simp

/-- (boundary `p = 1`): the root almost surely branches. -/
theorem law_one_root :
    law 1 zero_le_one le_rfl (branchAt []) = 1 ∧ law 1 zero_le_one le_rfl (leafAt []) = 0 := by
  have hbranch := law_root_branch (show (0 : ℝ) ≤ 1 from zero_le_one) (show (1 : ℝ) ≤ 1 from le_rfl)
  have hleaf := law_root_leaf (show (0 : ℝ) ≤ 1 from zero_le_one) (show (1 : ℝ) ≤ 1 from le_rfl)
  constructor
  · rw [hbranch]
    simp
  · rw [hleaf]
    norm_num

/-! ## exact prefix shifts

The subtree below prefix `u` is read by prepending the prefix in the
address: `(shift u ω) a = ω (u ++ a)`. These are the exact shifts the
grammar consumer (termination-depth leaf) inverts: its successor event
is the root-leaf event union the root-branch event intersected with the
inverse images of the depth event under `shiftLeft` and `shiftRight`. -/

/-- reindex a configuration to the subtree below prefix `u`. -/
def shift (u : List Bool) (ω : Ω) : Ω :=
  fun a => ω (u ++ a)

/-- reindex to the left subtree (root step `false`). -/
def shiftLeft (ω : Ω) : Ω :=
  shift [false] ω

/-- reindex to the right subtree (root step `true`). -/
def shiftRight (ω : Ω) : Ω :=
  shift [true] ω

theorem shift_apply (u : List Bool) (ω : Ω) (a : List Bool) :
    shift u ω a = ω (u ++ a) := by
  rfl

theorem shift_nil (ω : Ω) :
    shift [] ω = ω := by
  rfl

/-- shifting by a concatenated prefix is shifting twice:
first by the outer prefix `u`, then by `v` inside that subtree. -/
theorem shift_append (u v : List Bool) (ω : Ω) :
    shift (u ++ v) ω = shift v (shift u ω) := by
  funext a
  simp [shift, List.append_assoc]

theorem shiftLeft_apply (ω : Ω) (a : List Bool) :
    shiftLeft ω a = ω (false :: a) := by
  rfl

theorem shiftRight_apply (ω : Ω) (a : List Bool) :
    shiftRight ω a = ω (true :: a) := by
  rfl

theorem measurable_shift (u : List Bool) :
    Measurable (shift u) := by
  apply Measurable.of_eval
  intro a
  simp only [shift]
  exact measurable_pi_apply _

/-- the inverse image of a branch event under a prefix shift is
the branch event at the prefixed address. -/
theorem shift_preimage_branchAt (u a : List Bool) :
    shift u ⁻¹' branchAt a = branchAt (u ++ a) := by
  ext ω
  simp [shift, branchAt]

theorem shift_preimage_leafAt (u a : List Bool) :
    shift u ⁻¹' leafAt a = leafAt (u ++ a) := by
  ext ω
  simp [shift, leafAt]

theorem shiftLeft_preimage_branchAt (a : List Bool) :
    shiftLeft ⁻¹' branchAt a = branchAt (false :: a) := by
  ext ω
  simp [shiftLeft, shift, branchAt]

theorem shiftRight_preimage_branchAt (a : List Bool) :
    shiftRight ⁻¹' branchAt a = branchAt (true :: a) := by
  ext ω
  simp [shiftRight, shift, branchAt]

/-- the inverse image of a finite cylinder under a prefix shift,
in the membership form the depth consumer unfolds. -/
theorem shift_preimage_cylinder (u : List Bool) (s : Finset (List Bool))
    (t : List Bool → Bool) :
    shift u ⁻¹' cylinder s t = {ω : Ω | ∀ a ∈ s, ω (u ++ a) = t a} := by
  rfl

/-- every prefix shift preserves `law p hp0 hp1` (the shifted coordinates
are still independent `bernoulliBool p hp0 hp1` coordinates), by
`Measure.map_infinitePi_infinitePi_of_inj`. -/
theorem map_shift_law {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u : List Bool) :
    (law p hp0 hp1).map (shift u) = law p hp0 hp1 := by
  haveI : ∀ i : List Bool, IsProbabilityMeasure ((fun _ : List Bool => bernoulliBool p hp0 hp1) i) :=
    fun _ => bernoulliBool_isProbabilityMeasure hp0 hp1
  haveI : ∀ i : List Bool,
      IsProbabilityMeasure ((fun _ : List Bool => bernoulliBool p hp0 hp1) (u ++ i)) :=
    fun _ => bernoulliBool_isProbabilityMeasure hp0 hp1
  haveI : ∀ i : List Bool, IsProbabilityMeasure (bernoulliBool p hp0 hp1) :=
    fun _ => bernoulliBool_isProbabilityMeasure hp0 hp1
  have h := @MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj (List Bool) (List Bool)
    (fun _ => Bool) (fun _ => inferInstance) (fun _ : List Bool => bernoulliBool p hp0 hp1)
    (fun _ => bernoulliBool_isProbabilityMeasure hp0 hp1) (fun a : List Bool => u ++ a)
    (List.append_right_injective u)
  rw [law_eq_infinitePi hp0 hp1]
  show Measure.map (fun ω i => ω (u ++ i))
      (Measure.infinitePi fun _ : List Bool => bernoulliBool p hp0 hp1) =
    Measure.infinitePi fun _ : List Bool => bernoulliBool p hp0 hp1
  exact h

theorem law_shift_preimage {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u : List Bool)
    {E : Set Ω} (hE : MeasurableSet E) :
    law p hp0 hp1 (shift u ⁻¹' E) = law p hp0 hp1 E := by
  rw [← Measure.map_apply (measurable_shift u) hE, map_shift_law hp0 hp1 u]

end Cslib.Language.BinaryTreeAddressLaw
