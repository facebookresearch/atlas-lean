/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Bernoulli

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

/-! ## NEW: the coordinate law and the address law -/

/-- NEW: the sample space. One Bool choice per finite binary address:
`true` = branch, `false` = leaf. Abbreviation only; it is definitionally
`List Bool -> Bool` and introduces no tree or process structure. -/
abbrev Ω : Type :=
  List Bool → Bool

/-- NEW: Bernoulli(p) on one Bool coordinate, real parameter form of the
leaf contract: mass `p` on `true` (branch), mass `1 - p` on `false`
(leaf). For `p` outside `[0, 1]` the `ENNReal.ofReal` masses are a junk
value (not a probability measure); every probability statement below assumes
`0 <= p <= 1`. -/
noncomputable def bernoulliBool (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

/-- NEW (proposed symbol `law`): the independent branch-choice law on
`Ω = List Bool -> Bool`, the constant-family instance of
`MeasureTheory.Measure.infinitePi` with coordinate law `bernoulliBool p`
at every address. Unconditional as a measure; it is a probability
measure exactly on `0 <= p <= 1` (`law_isProbabilityMeasure`). -/
noncomputable def law (p : ℝ) : Measure Ω :=
  Measure.infinitePi (fun _ : List Bool => bernoulliBool p)

theorem law_def (p : ℝ) :
    law p = Measure.infinitePi (fun _ : List Bool => bernoulliBool p) := by
  rfl

/-- NEW: bridge to Mathlib's unit-interval Bernoulli measure. -/
theorem bernoulliBool_eq_bernoulliMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bernoulliBool p = ProbabilityTheory.bernoulliMeasure true false ⟨p, hp0, hp1⟩ := by
  unfold bernoulliBool ProbabilityTheory.bernoulliMeasure
  have h0 : (0 : ℝ) ≤ 1 - p := by linarith
  have h1 : (unitInterval.toNNReal ⟨p, hp0, hp1⟩ : ℝ≥0∞) = ENNReal.ofReal p := by
    have h_eq : unitInterval.toNNReal ⟨p, hp0, hp1⟩ = NNReal.mk p hp0 := rfl
    rw [h_eq, ← ENNReal.ofReal_eq_coe_nnreal hp0]
  have h2 : (unitInterval.toNNReal (unitInterval.symm ⟨p, hp0, hp1⟩) : ℝ≥0∞)
      = ENNReal.ofReal (1 - p) := by
    have h_eq : unitInterval.toNNReal (unitInterval.symm ⟨p, hp0, hp1⟩) = NNReal.mk (1 - p) h0 := rfl
    rw [h_eq, ← ENNReal.ofReal_eq_coe_nnreal h0]
  rw [← h1, ← h2, MeasureTheory.Measure.coe_nnreal_smul, MeasureTheory.Measure.coe_nnreal_smul]

theorem bernoulliBool_isProbabilityMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliBool p) := by
  rw [bernoulliBool_eq_bernoulliMeasure hp0 hp1]
  infer_instance

/-- NEW: coordinate masses, no range hypothesis needed. -/
theorem bernoulliBool_apply_true (p : ℝ) :
    bernoulliBool p {true} = ENNReal.ofReal p := by
  unfold bernoulliBool
  simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul]

theorem bernoulliBool_apply_false (p : ℝ) :
    bernoulliBool p {false} = ENNReal.ofReal (1 - p) := by
  unfold bernoulliBool
  simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul]

theorem law_isProbabilityMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (law p) := by
  haveI : ∀ _ : List Bool, IsProbabilityMeasure (bernoulliBool p) :=
    fun _ => bernoulliBool_isProbabilityMeasure hp0 hp1
  unfold law
  infer_instance

/-- NEW: each address coordinate of `law p` is `bernoulliBool p`
(`Measure.infinitePi_map_eval` at the constant family). -/
theorem law_map_eval {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a : List Bool) :
    (law p).map (fun ω : Ω => ω a) = bernoulliBool p := by
  have hInst : ∀ i : List Bool, IsProbabilityMeasure ((fun _ : List Bool => bernoulliBool p) i) :=
    fun _ => bernoulliBool_isProbabilityMeasure hp0 hp1
  unfold law
  exact @Measure.infinitePi_map_eval (List Bool) (fun _ => Bool) _ (fun _ => bernoulliBool p) hInst a

/-! ## NEW: finite-address cylinders and their masses -/

/-- NEW: the finite-address cylinder fixing the choices on the finset
`s` to the assignment `t`, leaving every address outside `s` (in
particular every descendant of a leaf in `s`) unrestricted. This is a
plain finite-coordinate event, not a tree type. -/
def cylinder (s : Finset (List Bool)) (t : List Bool → Bool) : Set Ω :=
  {ω : Ω | ∀ a ∈ s, ω a = t a}

/-- NEW (proposed symbol `cylinder_mass`): the product mass of
`cylinder s t` under `law p`: one factor `p` per address assigned
`true` (branch) and one factor `1 - p` per address assigned `false`
(leaf). -/
noncomputable def cylinder_mass (p : ℝ) (s : Finset (List Bool)) (t : List Bool → Bool) :
    ℝ≥0∞ :=
  ∏ a ∈ s, (if t a then ENNReal.ofReal p else ENNReal.ofReal (1 - p))

theorem mem_cylinder {s : Finset (List Bool)} {t : List Bool → Bool} {ω : Ω} :
    ω ∈ cylinder s t ↔ ∀ a ∈ s, ω a = t a := by
  rfl

/-- NEW: the finite-product formula for `law p`, directly
`Measure.infinitePi_pi` at the constant family. -/
theorem law_pi {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Finset (List Bool))
    (T : List Bool → Set Bool) (hT : ∀ a ∈ s, MeasurableSet (T a)) :
    law p ((s : Set (List Bool)).pi T) = ∏ a ∈ s, bernoulliBool p (T a) := by
  have hInst : ∀ i : List Bool, IsProbabilityMeasure ((fun _ : List Bool => bernoulliBool p) i) :=
    fun _ => bernoulliBool_isProbabilityMeasure hp0 hp1
  unfold law
  exact @Measure.infinitePi_pi (List Bool) (fun _ => Bool) _ (fun _ => bernoulliBool p) hInst s T hT

/-- NEW: the same formula in Mathlib's `MeasureTheory.cylinder` form,
directly `Measure.infinitePi_cylinder` at the constant family. -/
theorem law_mathlib_cylinder {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Finset (List Bool)) {S : Set (∀ _ : s, Bool)} (hS : MeasurableSet S) :
    law p (MeasureTheory.cylinder s S) =
      Measure.pi (fun _ : s => bernoulliBool p) S := by
  have hInst : ∀ i : List Bool, IsProbabilityMeasure ((fun _ : List Bool => bernoulliBool p) i) :=
    fun _ => bernoulliBool_isProbabilityMeasure hp0 hp1
  unfold law
  exact @Measure.infinitePi_cylinder (List Bool) (fun _ => Bool) _ (fun _ => bernoulliBool p) hInst s S hS

/-- NEW: the headline cylinder probability. -/
theorem law_cylinder {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Finset (List Bool)) (t : List Bool → Bool) :
    law p (cylinder s t) = cylinder_mass p s t := by
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

/-- NEW: `cylinder_mass` is the product of the coordinate singleton
masses, the bridge between the two formulas above. -/
theorem cylinder_mass_eq_prod {p : ℝ} (s : Finset (List Bool)) (t : List Bool → Bool) :
    cylinder_mass p s t = ∏ a ∈ s, bernoulliBool p {t a} := by
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
    law p (cylinder ∅ t) = 1 := by
  have h : IsProbabilityMeasure (law p) := law_isProbabilityMeasure hp0 hp1
  rw [cylinder_empty, @measure_univ Ω _ (law p) h]

theorem cylinder_mass_insert {p : ℝ} {a : List Bool} {s : Finset (List Bool)}
    (ha : a ∉ s) (t : List Bool → Bool) :
    cylinder_mass p (insert a s) t =
      (if t a then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) * cylinder_mass p s t := by
  simp [cylinder_mass, Finset.prod_insert ha]

theorem cylinder_mass_singleton {p : ℝ} (a : List Bool) (t : List Bool → Bool) :
    cylinder_mass p {a} t =
      (if t a then ENNReal.ofReal p else ENNReal.ofReal (1 - p)) := by
  simp [cylinder_mass]

/-! ## NEW: root choice, left/right cylinders, boundary probabilities -/

/-- NEW: the event that the node at address `a` branches. -/
def branchAt (a : List Bool) : Set Ω :=
  {ω : Ω | ω a = true}

/-- NEW: the event that the node at address `a` is a leaf. -/
def leafAt (a : List Bool) : Set Ω :=
  {ω : Ω | ω a = false}

theorem branchAt_eq_cylinder (a : List Bool) :
    branchAt a = cylinder {a} (fun _ => true) := by
  ext ω
  simp [branchAt, cylinder]

theorem leafAt_eq_cylinder (a : List Bool) :
    leafAt a = cylinder {a} (fun _ => false) := by
  ext ω
  simp [leafAt, cylinder]

/-- NEW (nonvacuity, root choice): the root branches with mass `p`. -/
theorem law_root_branch {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    law p (branchAt []) = ENNReal.ofReal p := by
  rw [branchAt_eq_cylinder, law_cylinder hp0 hp1, cylinder_mass_singleton]
  simp

/-- NEW (nonvacuity, root choice): the root is a leaf with mass `1 - p`. -/
theorem law_root_leaf {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    law p (leafAt []) = ENNReal.ofReal (1 - p) := by
  rw [leafAt_eq_cylinder, law_cylinder hp0 hp1, cylinder_mass_singleton]
  simp

/-- NEW: two cylinders on the same finset that disagree at one address
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

/-- NEW: branch and leaf events at one address are disjoint. -/
theorem branchAt_disjoint_leafAt (a : List Bool) :
    Disjoint (branchAt a) (leafAt a) := by
  rw [Set.disjoint_left]
  intro ω h1 h2
  simp [branchAt, leafAt] at h1 h2
  rw [h1] at h2
  simp at h2

/-- NEW (nonvacuity, disjoint left cylinders): the two choices at the
left-child address `[false]` are disjoint. -/
theorem disjoint_left_cylinders :
    Disjoint (cylinder {[false]} (fun _ => true)) (cylinder {[false]} (fun _ => false)) := by
  exact cylinder_disjoint_of_ne (Finset.mem_singleton_self _) (by simp)

/-- NEW (nonvacuity, disjoint right cylinders): the two choices at the
right-child address `[true]` are disjoint. -/
theorem disjoint_right_cylinders :
    Disjoint (cylinder {[true]} (fun _ => true)) (cylinder {[true]} (fun _ => false)) := by
  exact cylinder_disjoint_of_ne (Finset.mem_singleton_self _) (by simp)

/-- NEW (boundary coordinate laws). -/
theorem bernoulliBool_zero :
    bernoulliBool 0 = Measure.dirac false := by
  unfold bernoulliBool
  simp

theorem bernoulliBool_one :
    bernoulliBool 1 = Measure.dirac true := by
  unfold bernoulliBool
  simp

/-- NEW (boundary `p = 0`): the root is almost surely a leaf. -/
theorem law_zero_root :
    law 0 (leafAt []) = 1 ∧ law 0 (branchAt []) = 0 := by
  have hleaf := law_root_leaf (show (0 : ℝ) ≤ 0 from le_rfl) (show (0 : ℝ) ≤ 1 from zero_le_one)
  have hbranch := law_root_branch (show (0 : ℝ) ≤ 0 from le_rfl) (show (0 : ℝ) ≤ 1 from zero_le_one)
  constructor
  · rw [hleaf]
    norm_num
  · rw [hbranch]
    simp

/-- NEW (boundary `p = 1`): the root almost surely branches. -/
theorem law_one_root :
    law 1 (branchAt []) = 1 ∧ law 1 (leafAt []) = 0 := by
  have hbranch := law_root_branch (show (0 : ℝ) ≤ 1 from zero_le_one) (show (1 : ℝ) ≤ 1 from le_rfl)
  have hleaf := law_root_leaf (show (0 : ℝ) ≤ 1 from zero_le_one) (show (1 : ℝ) ≤ 1 from le_rfl)
  constructor
  · rw [hbranch]
    simp
  · rw [hleaf]
    norm_num

/-! ## NEW: exact prefix shifts

The subtree below prefix `u` is read by prepending the prefix in the
address: `(shift u ω) a = ω (u ++ a)`. These are the exact shifts the
grammar consumer (termination-depth leaf) inverts: its successor event
is the root-leaf event union the root-branch event intersected with the
inverse images of the depth event under `shiftLeft` and `shiftRight`. -/

/-- NEW: reindex a configuration to the subtree below prefix `u`. -/
def shift (u : List Bool) (ω : Ω) : Ω :=
  fun a => ω (u ++ a)

/-- NEW: reindex to the left subtree (root step `false`). -/
def shiftLeft (ω : Ω) : Ω :=
  shift [false] ω

/-- NEW: reindex to the right subtree (root step `true`). -/
def shiftRight (ω : Ω) : Ω :=
  shift [true] ω

theorem shift_apply (u : List Bool) (ω : Ω) (a : List Bool) :
    shift u ω a = ω (u ++ a) := by
  rfl

theorem shift_nil (ω : Ω) :
    shift [] ω = ω := by
  rfl

/-- NEW: shifting by a concatenated prefix is shifting twice:
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

/-- NEW: the inverse image of a branch event under a prefix shift is
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

/-- NEW: the inverse image of a finite cylinder under a prefix shift,
in the membership form the depth consumer unfolds. -/
theorem shift_preimage_cylinder (u : List Bool) (s : Finset (List Bool))
    (t : List Bool → Bool) :
    shift u ⁻¹' cylinder s t = {ω : Ω | ∀ a ∈ s, ω (u ++ a) = t a} := by
  rfl

/-- NEW: every prefix shift preserves `law p` (the shifted coordinates
are still independent `bernoulliBool p` coordinates), by
`Measure.eq_infinitePi`. -/
theorem map_shift_law {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u : List Bool) :
    (law p).map (shift u) = law p := by
  have hInst : ∀ i : List Bool, IsProbabilityMeasure ((fun _ : List Bool => bernoulliBool p) i) :=
    fun _ => bernoulliBool_isProbabilityMeasure hp0 hp1
  unfold law
  apply @Measure.eq_infinitePi (List Bool) (fun _ => Bool) _ (fun _ => bernoulliBool p) hInst _
  intro s t ht
  have hmeas : MeasurableSet ((s : Set (List Bool)).pi t) :=
    MeasurableSet.pi (Finset.countable_toSet s) (fun i _ => ht i)
  rw [@Measure.map_apply Ω Ω _ _ _ (shift u) (measurable_shift u) _ hmeas]
  have hf_inj : Function.Injective (fun a : List Bool => u ++ a) :=
    List.append_right_injective u
  let e : List Bool ↪ List Bool := ⟨fun a => u ++ a, hf_inj⟩
  have heq : ∀ a : List Bool, e a = u ++ a := fun _ => rfl
  let t' : List Bool → Set Bool := fun b => {y | ∃ a ∈ s, u ++ a = b ∧ y ∈ t a}
  have ht'_eq : ∀ a₀ ∈ s, t' (u ++ a₀) = t a₀ := by
    intro a₀ ha₀
    ext y
    simp only [t', Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, ha, heq2, hy⟩
      have : a = a₀ := hf_inj heq2
      subst this
      exact hy
    · intro hy
      exact ⟨a₀, ha₀, rfl, hy⟩
  have ht'_eq_e : ∀ a₀ ∈ s, t' (e a₀) = t a₀ := by
    intro a₀ ha₀
    rw [heq]
    exact ht'_eq a₀ ha₀
  have ht'_meas : ∀ b ∈ s.map e, MeasurableSet (t' b) := by
    intro b hb
    rw [Finset.mem_map] at hb
    obtain ⟨a, ha, hab⟩ := hb
    rw [← hab]
    exact ht'_eq_e a ha ▸ ht a
  have hpre_eq : shift u ⁻¹' ((s : Set (List Bool)).pi t)
      = ((s.map e : Finset (List Bool)) : Set (List Bool)).pi t' := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, shift]
    constructor
    · intro h b hb
      rw [Finset.mem_map] at hb
      obtain ⟨a, ha, hab⟩ := hb
      rw [← hab, heq]
      have ha_coe : a ∈ (s : Set (List Bool)) := Finset.mem_coe.mpr ha
      have h_a := h a ha_coe
      rw [ht'_eq a ha]
      exact h_a
    · intro h a ha
      have ha_fin : a ∈ s := Finset.mem_coe.mp ha
      have hb : e a ∈ s.map e := Finset.mem_map.mpr ⟨a, ha_fin, rfl⟩
      have hb_coe : (e a : List Bool) ∈ ((s.map e : Finset (List Bool)) : Set (List Bool)) :=
        Finset.mem_coe.mpr hb
      have h_b := h (e a) hb_coe
      rw [heq, ht'_eq a ha_fin] at h_b
      exact h_b
  rw [hpre_eq]
  have hpi : Measure.infinitePi (fun _ : List Bool => bernoulliBool p)
      (((s.map e : Finset (List Bool)) : Set (List Bool)).pi t')
      = ∏ b ∈ s.map e, bernoulliBool p (t' b) := by
    exact @Measure.infinitePi_pi (List Bool) (fun _ => Bool) _ (fun _ => bernoulliBool p) hInst (s.map e) t' ht'_meas
  rw [hpi]
  rw [Finset.prod_map s e (fun b => bernoulliBool p (t' b))]
  apply Finset.prod_congr rfl
  intro a ha
  rw [ht'_eq_e a ha]

theorem law_shift_preimage {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u : List Bool)
    {E : Set Ω} (hE : MeasurableSet E) :
    law p (shift u ⁻¹' E) = law p E := by
  rw [← Measure.map_apply (measurable_shift u) hE, map_shift_law hp0 hp1 u]

/-! ## PIN-TEST: concrete checks (move to CSLibExtTest on port) -/

end Cslib.Language.BinaryTreeAddressLaw
