/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.TopologicalEntropy.Compact
import MathlibExt.Dynamics.SymbolicDynamics.FullShift

/-!
# Tests for topological entropy on compact R1 spaces

This module tests `Dynamics.topologicalEntropy` on the two-sided full shift
on two symbols. The positive lower bound `log 2` comes from counting
dynamical covers. The identity map has entropy `0`, so positivity is sharp:
the zero case is the near-miss showing the bound is not vacuous.
-/

namespace TopologicalEntropyCompactTests

/-- Pairs of configurations agreeing at coordinate zero. -/
def U0 :
    SetRel (SymbolicDynamics.FullShift.FullShiftSpace 2)
      (SymbolicDynamics.FullShift.FullShiftSpace 2) :=
  {p | p.1 0 = p.2 0}

/-- `U0` is open in the product topology. -/
theorem U0_isOpen : IsOpen U0 := by
  have hcont :
      Continuous
        (fun p :
          SymbolicDynamics.FullShift.FullShiftSpace 2 ×
            SymbolicDynamics.FullShift.FullShiftSpace 2 =>
          (p.1 0, p.2 0)) := by
    exact
      ((continuous_apply 0).comp continuous_fst).prodMk
        ((continuous_apply 0).comp continuous_snd)
  have hdiag : IsOpen (Set.diagonal (Fin 2)) := isOpen_discrete _
  have heq : U0 =
      (fun p :
        SymbolicDynamics.FullShift.FullShiftSpace 2 ×
          SymbolicDynamics.FullShift.FullShiftSpace 2 =>
        (p.1 0, p.2 0)) ⁻¹' Set.diagonal (Fin 2) :=
    rfl
  rw [heq]
  exact hdiag.preimage hcont

/-- `U0` is an entourage for the canonical uniformity. -/
theorem U0_mem :
    U0 ∈ @uniformity _ uniformSpaceOfCompactR1 := by
  have hsub :
      Set.diagonal
        (SymbolicDynamics.FullShift.FullShiftSpace 2) ⊆ U0 := by
    intro p hp
    have hpair : p.1 = p.2 := Set.mem_diagonal_iff.mp hp
    show p.1 0 = p.2 0
    rw [hpair]
  have hmem :
      U0 ∈
        nhdsSet
          (Set.diagonal
            (SymbolicDynamics.FullShift.FullShiftSpace 2)) :=
    U0_isOpen.mem_nhdsSet.mpr hsub
  have heq :
      nhdsSet
          (Set.diagonal
            (SymbolicDynamics.FullShift.FullShiftSpace 2)) =
        @uniformity
          (SymbolicDynamics.FullShift.FullShiftSpace 2)
          uniformSpaceOfCompactR1 :=
    @nhdsSet_diagonal_eq_uniformity
      (SymbolicDynamics.FullShift.FullShiftSpace 2)
      uniformSpaceOfCompactR1 inferInstance
  rwa [heq] at hmem

/-- Iterates of the full shift read later coordinates. -/
theorem shift_iterate
    (x : SymbolicDynamics.FullShift.FullShiftSpace 2)
    (k : ℕ) (i : ℤ) :
    (SymbolicDynamics.FullShift.unitShift 2)^[k] x i =
      x ((k : ℤ) + i) := by
  induction k generalizing x i with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih,
      SymbolicDynamics.FullShift.unitShift_apply]
    congr 1
    push_cast
    ring

/-- Dynamical entourage for `U0` compares the first `n` coordinates. -/
theorem dyn_shift_eq (n : ℕ)
    (x y : SymbolicDynamics.FullShift.FullShiftSpace 2) :
    (x, y) ∈
        Dynamics.dynEntourage
          (SymbolicDynamics.FullShift.unitShift 2) U0 n ↔
      ∀ k < n, x (k : ℤ) = y (k : ℤ) := by
  rw [Dynamics.mem_dynEntourage]
  constructor
  · intro h k hk
    have hmem := h k hk
    have h1 :
        (SymbolicDynamics.FullShift.unitShift 2)^[k] x 0 =
          x (k : ℤ) := by
      simp [shift_iterate]
    have h2 :
        (SymbolicDynamics.FullShift.unitShift 2)^[k] y 0 =
          y (k : ℤ) := by
      simp [shift_iterate]
    have h3 :
        (SymbolicDynamics.FullShift.unitShift 2)^[k] x 0 =
          (SymbolicDynamics.FullShift.unitShift 2)^[k] y 0 :=
      hmem
    rw [h1, h2] at h3
    exact h3
  · intro h k hk
    have h1 :
        (SymbolicDynamics.FullShift.unitShift 2)^[k] x 0 =
          x (k : ℤ) := by
      simp [shift_iterate]
    have h2 :
        (SymbolicDynamics.FullShift.unitShift 2)^[k] y 0 =
          y (k : ℤ) := by
      simp [shift_iterate]
    show
      (SymbolicDynamics.FullShift.unitShift 2)^[k] x 0 =
        (SymbolicDynamics.FullShift.unitShift 2)^[k] y 0
    rw [h1, h2]
    exact h k hk

/-- Every dynamical cover needs at least `2 ^ n` points. -/
theorem card_le (n : ℕ) :
    (2 ^ n : ℕ∞) ≤
      Dynamics.coverMincard
        (SymbolicDynamics.FullShift.unitShift 2) Set.univ U0
        n := by
  apply le_iInf
  intro s
  apply le_iInf
  intro h
  have hcard_nat : (2 ^ n : ℕ) ≤ s.card := by
    classical
    have hcardF : Fintype.card (Fin n → Fin 2) = 2 ^ n := by
      simp
    let mk : (Fin n → Fin 2) →
        SymbolicDynamics.FullShift.FullShiftSpace 2 :=
      fun f i =>
        if hh : i.toNat < n then f ⟨i.toNat, hh⟩ else 0
    have hmk : ∀ (f : Fin n → Fin 2) (k : ℕ) (hk : k < n),
        mk f (k : ℤ) = f ⟨k, hk⟩ := by
      intro f k hk
      show
        (if hh : ((k : ℤ)).toNat < n then
          f ⟨((k : ℤ)).toNat, hh⟩ else 0) = f ⟨k, hk⟩
      have hto : ((k : ℤ)).toNat = k := by simp
      rw [hto]
      simp [hk]
    have hcov : ∀ f : Fin n → Fin 2,
        ∃ y ∈ (↑s : Set
          (SymbolicDynamics.FullShift.FullShiftSpace 2)),
          (mk f, y) ∈
            Dynamics.dynEntourage
              (SymbolicDynamics.FullShift.unitShift 2) U0 n := by
      intro f
      exact h (Set.mem_univ (mk f))
    choose g hg using hcov
    let G : (Fin n → Fin 2) → ↥s := fun f =>
      ⟨g f, Finset.mem_coe.mp (hg f).1⟩
    have hinj : Function.Injective G := by
      intro f1 f2 heq
      have hval : g f1 = g f2 := congrArg Subtype.val heq
      have h1 := (hg f1).2
      have h2 := (hg f2).2
      rw [dyn_shift_eq] at h1 h2
      apply funext
      intro a
      obtain ⟨k, hk⟩ := a
      have e1 : mk f1 (k : ℤ) = g f1 (k : ℤ) := h1 k hk
      have e2 : mk f2 (k : ℤ) = g f2 (k : ℤ) := h2 k hk
      rw [hmk f1 k hk] at e1
      rw [hmk f2 k hk] at e2
      rw [hval] at e1
      exact e1.trans e2.symm
    have hle :
        Fintype.card (Fin n → Fin 2) ≤ Fintype.card ↥s :=
      Fintype.card_le_of_injective G hinj
    rw [hcardF, Fintype.card_coe] at hle
    exact hle
  exact_mod_cast hcard_nat

/-- Log-two lower bound for the full shift. -/
theorem log_two_le :
    ((Real.log 2 : ℝ) : EReal) ≤
      Dynamics.topologicalEntropy
        (SymbolicDynamics.FullShift.unitShift 2) := by
  have hU : U0 ∈
      @uniformity
        (SymbolicDynamics.FullShift.FullShiftSpace 2)
        uniformSpaceOfCompactR1 :=
    U0_mem
  have hle1 :
      Dynamics.coverEntropyEntourage
          (SymbolicDynamics.FullShift.unitShift 2) Set.univ U0 ≤
        @Dynamics.coverEntropy
          (SymbolicDynamics.FullShift.FullShiftSpace 2)
          uniformSpaceOfCompactR1
          (SymbolicDynamics.FullShift.unitShift 2) Set.univ :=
    @Dynamics.coverEntropyEntourage_le_coverEntropy
      (SymbolicDynamics.FullShift.FullShiftSpace 2) U0
      uniformSpaceOfCompactR1 _ _ hU
  have heq :
      @Dynamics.coverEntropy
          (SymbolicDynamics.FullShift.FullShiftSpace 2)
          uniformSpaceOfCompactR1
          (SymbolicDynamics.FullShift.unitShift 2) Set.univ =
        Dynamics.topologicalEntropy
          (SymbolicDynamics.FullShift.unitShift 2) :=
    Dynamics.coverEntropy_eq_topologicalEntropy
      uniformSpaceOfCompactR1 rfl _
  have hlow :
      ((Real.log 2 : ℝ) : EReal) ≤
        Dynamics.coverEntropyEntourage
          (SymbolicDynamics.FullShift.unitShift 2) Set.univ
          U0 := by
    have hdef :
        Dynamics.coverEntropyEntourage
            (SymbolicDynamics.FullShift.unitShift 2) Set.univ
            U0 =
          ExpGrowth.expGrowthSup (fun n =>
            Dynamics.coverMincard
              (SymbolicDynamics.FullShift.unitShift 2) Set.univ
              U0 n) :=
      rfl
    have hle_n : ∀ n : ℕ, (2 : ENNReal) ^ n ≤
        ↑(Dynamics.coverMincard
          (SymbolicDynamics.FullShift.unitShift 2) Set.univ U0
          n) := by
      intro n
      have hNat : ((((2 ^ n : ℕ) : ℕ∞))) = (2 ^ n : ℕ∞) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
      have hcast : (↑((2 ^ n : ℕ∞)) : ENNReal) =
          (2 : ENNReal) ^ n := by
        rw [← hNat, ENat.toENNReal_coe, Nat.cast_pow,
          Nat.cast_ofNat]
      have hEN : (↑((2 ^ n : ℕ∞)) : ENNReal) ≤
          ↑(Dynamics.coverMincard
            (SymbolicDynamics.FullShift.unitShift 2) Set.univ
            U0 n) :=
        ENat.toENNReal_le.mpr (card_le n)
      rw [hcast] at hEN
      exact hEN
    have hmono :
        ExpGrowth.expGrowthSup (fun n : ℕ =>
          (2 : ENNReal) ^ n) ≤
          ExpGrowth.expGrowthSup (fun n : ℕ =>
            ↑(Dynamics.coverMincard
              (SymbolicDynamics.FullShift.unitShift 2) Set.univ
              U0 n)) :=
      ExpGrowth.expGrowthSup_monotone fun n => hle_n n
    have hpow :
        ExpGrowth.expGrowthSup (fun n : ℕ =>
          (2 : ENNReal) ^ n) = (2 : ENNReal).log :=
      ExpGrowth.expGrowthSup_pow
    have hof : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by
      norm_cast
    have hpos : (0 : ℝ) < 2 := by norm_num
    have hlog2 : (2 : ENNReal).log =
        ((Real.log 2 : ℝ) : EReal) := by
      rw [← hof, ENNReal.log_ofReal_of_pos hpos]
    rw [hdef, ← hlog2, ← hpow]
    exact hmono
  exact hlow.trans (hle1.trans (le_of_eq heq))

/-- Positivity of entropy for the full shift. -/
theorem entropy_pos :
    0 <
      Dynamics.topologicalEntropy
        (SymbolicDynamics.FullShift.unitShift 2) := by
  have hlog_pos : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (by norm_num)
  have hlog_pos' : (0 : EReal) < ((Real.log 2 : ℝ) : EReal) := by
    exact_mod_cast hlog_pos
  exact lt_of_lt_of_le hlog_pos' log_two_le

/-- Product uniformity on the full shift from the discrete one on `Fin 2`. -/
@[instance_reducible]
noncomputable def piU :
    UniformSpace
      (SymbolicDynamics.FullShift.FullShiftSpace 2) := by
  letI : UniformSpace (Fin 2) := ⊥
  exact inferInstance

/-- Independence of the uniform structure, on the full shift. -/
theorem pi_cover_eq :
    @UniformSpace.toTopologicalSpace
        (SymbolicDynamics.FullShift.FullShiftSpace 2) piU =
        (inferInstance :
          TopologicalSpace
            (SymbolicDynamics.FullShift.FullShiftSpace 2)) ∧
      @Dynamics.coverEntropy
        (SymbolicDynamics.FullShift.FullShiftSpace 2) piU
        (SymbolicDynamics.FullShift.unitShift 2) Set.univ =
        Dynamics.topologicalEntropy
          (SymbolicDynamics.FullShift.unitShift 2) := by
  have htop :
      @UniformSpace.toTopologicalSpace
        (SymbolicDynamics.FullShift.FullShiftSpace 2) piU =
        (inferInstance :
          TopologicalSpace
            (SymbolicDynamics.FullShift.FullShiftSpace 2)) :=
    rfl
  exact
    ⟨htop,
      Dynamics.coverEntropy_eq_topologicalEntropy piU htop _⟩

/-- Iterates of the identity map fix every configuration. -/
theorem id_iterate
    (k : ℕ)
    (x : SymbolicDynamics.FullShift.FullShiftSpace 2) :
    (id :
      SymbolicDynamics.FullShift.FullShiftSpace 2 →
        SymbolicDynamics.FullShift.FullShiftSpace 2)^[k] x =
      x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hid : (id :
        SymbolicDynamics.FullShift.FullShiftSpace 2 →
          SymbolicDynamics.FullShift.FullShiftSpace 2) x = x :=
      rfl
    rw [Function.iterate_succ_apply, hid]
    exact ih

/-- For the identity, every `1`-step cover is an `n`-step cover. -/
theorem coverMincard_id_le
    (U :
      SetRel
        (SymbolicDynamics.FullShift.FullShiftSpace 2)
        (SymbolicDynamics.FullShift.FullShiftSpace 2))
    (n : ℕ) :
    Dynamics.coverMincard
        (id :
          SymbolicDynamics.FullShift.FullShiftSpace 2 →
            SymbolicDynamics.FullShift.FullShiftSpace 2)
        Set.univ U n ≤
      Dynamics.coverMincard
        (id :
          SymbolicDynamics.FullShift.FullShiftSpace 2 →
            SymbolicDynamics.FullShift.FullShiftSpace 2)
        Set.univ U 1 := by
  apply le_iInf
  intro s
  apply le_iInf
  intro h1
  apply Dynamics.IsDynCoverOf.coverMincard_le_card
  have hcov :
      ∀ x ∈
        (Set.univ :
          Set
            (SymbolicDynamics.FullShift.FullShiftSpace 2)),
        ∃ y ∈
          (↑s :
            Set
              (SymbolicDynamics.FullShift.FullShiftSpace 2)),
          (x, y) ∈
            Dynamics.dynEntourage
              (id :
                SymbolicDynamics.FullShift.FullShiftSpace 2 →
                  SymbolicDynamics.FullShift.FullShiftSpace 2)
              U n := by
    intro x hx
    obtain ⟨y, hys, hxy⟩ := h1 hx
    rw [Dynamics.mem_dynEntourage] at hxy
    have h0 : (0 : ℕ) < 1 := by norm_num
    have hbase : (x, y) ∈ U := hxy 0 h0
    refine ⟨y, hys, Dynamics.mem_dynEntourage.mpr ?_⟩
    intro k _
    have e1 :
        (id :
          SymbolicDynamics.FullShift.FullShiftSpace 2 →
            SymbolicDynamics.FullShift.FullShiftSpace 2)^[k]
          x =
        x :=
      id_iterate k x
    have e2 :
        (id :
          SymbolicDynamics.FullShift.FullShiftSpace 2 →
            SymbolicDynamics.FullShift.FullShiftSpace 2)^[k]
          y =
        y :=
      id_iterate k y
    rw [e1, e2]
    exact hbase
  exact hcov

/-- Cover entropy of the identity is nonpositive on each entourage. -/
theorem entourage_id_le_zero
    (U :
      SetRel
        (SymbolicDynamics.FullShift.FullShiftSpace 2)
        (SymbolicDynamics.FullShift.FullShiftSpace 2))
    (hU :
      U ∈
        @uniformity
          (SymbolicDynamics.FullShift.FullShiftSpace 2)
          uniformSpaceOfCompactR1) :
    Dynamics.coverEntropyEntourage
        (id :
          SymbolicDynamics.FullShift.FullShiftSpace 2 →
            SymbolicDynamics.FullShift.FullShiftSpace 2)
        Set.univ U ≤
      0 := by
  have hfin :
      Dynamics.coverMincard
        (id :
          SymbolicDynamics.FullShift.FullShiftSpace 2 →
            SymbolicDynamics.FullShift.FullShiftSpace 2)
        Set.univ U 1 <
      ⊤ :=
    @Dynamics.coverMincard_finite_of_isCompact_invariant
      (SymbolicDynamics.FullShift.FullShiftSpace 2)
      (id :
        SymbolicDynamics.FullShift.FullShiftSpace 2 →
          SymbolicDynamics.FullShift.FullShiftSpace 2)
      U Set.univ uniformSpaceOfCompactR1 isCompact_univ
      (fun x _ => Set.mem_univ (id x)) hU 1
  have hne :
      Dynamics.coverMincard
        (id :
          SymbolicDynamics.FullShift.FullShiftSpace 2 →
            SymbolicDynamics.FullShift.FullShiftSpace 2)
        Set.univ U 1 ≠
      ⊤ :=
    ne_of_lt hfin
  have h1s :
      ∀ s :
        Finset
          (SymbolicDynamics.FullShift.FullShiftSpace 2),
        Dynamics.IsDynCoverOf
            (id :
              SymbolicDynamics.FullShift.FullShiftSpace 2 →
                SymbolicDynamics.FullShift.FullShiftSpace 2)
            Set.univ U 1 (↑s : Set
              (SymbolicDynamics.FullShift.FullShiftSpace 2)) →
          1 ≤ s.card := by
    intro s hs
    obtain ⟨y, hys, _hxy⟩ :=
      hs (Set.mem_univ (fun _ => (0 : Fin 2)))
    have hmem : y ∈ s := Finset.mem_coe.mp hys
    have hpos : 0 < s.card :=
      Finset.card_pos.mpr ⟨y, hmem⟩
    omega
  have h1m :
      (1 : ℕ∞) ≤
        Dynamics.coverMincard
          (id :
            SymbolicDynamics.FullShift.FullShiftSpace 2 →
              SymbolicDynamics.FullShift.FullShiftSpace 2)
          Set.univ U 1 := by
    apply le_iInf
    intro s
    apply le_iInf
    intro hs
    exact_mod_cast h1s s hs
  have htop_eq : ((⊤ : ℕ∞) : ENNReal) = ⊤ := by simp
  have h11 : ((1 : ℕ∞) : ENNReal) = 1 := by simp
  have hb_top :
      (↑(Dynamics.coverMincard
        (id :
          SymbolicDynamics.FullShift.FullShiftSpace 2 →
            SymbolicDynamics.FullShift.FullShiftSpace 2)
        Set.univ U 1) :
        ENNReal) ≠
      ⊤ := by
    intro hcon
    apply hne
    have hle1 :
        ((⊤ : ℕ∞) : ENNReal) ≤
          ↑(Dynamics.coverMincard
            (id :
              SymbolicDynamics.FullShift.FullShiftSpace 2 →
                SymbolicDynamics.FullShift.FullShiftSpace 2)
            Set.univ U 1) := by
      rw [htop_eq, hcon]
    have hle2 :
        (⊤ : ℕ∞) ≤
          Dynamics.coverMincard
            (id :
              SymbolicDynamics.FullShift.FullShiftSpace 2 →
                SymbolicDynamics.FullShift.FullShiftSpace 2)
            Set.univ U 1 :=
      ENat.toENNReal_le.mp hle1
    exact top_le_iff.mp hle2
  have h1b :
      (1 : ENNReal) ≤
        ↑(Dynamics.coverMincard
          (id :
            SymbolicDynamics.FullShift.FullShiftSpace 2 →
              SymbolicDynamics.FullShift.FullShiftSpace 2)
          Set.univ U 1) :=
    h11 ▸ ENat.toENNReal_le.mpr h1m
  have hbpos :
      (0 : ENNReal) <
        ↑(Dynamics.coverMincard
          (id :
            SymbolicDynamics.FullShift.FullShiftSpace 2 →
              SymbolicDynamics.FullShift.FullShiftSpace 2)
          Set.univ U 1) :=
    lt_of_lt_of_le zero_lt_one h1b
  have hb_zero :
      (↑(Dynamics.coverMincard
        (id :
          SymbolicDynamics.FullShift.FullShiftSpace 2 →
            SymbolicDynamics.FullShift.FullShiftSpace 2)
        Set.univ U 1) :
        ENNReal) ≠
      0 :=
    ne_of_gt hbpos
  have hdef :
      Dynamics.coverEntropyEntourage
        (id :
          SymbolicDynamics.FullShift.FullShiftSpace 2 →
            SymbolicDynamics.FullShift.FullShiftSpace 2)
        Set.univ U =
      ExpGrowth.expGrowthSup (fun n =>
        Dynamics.coverMincard
          (id :
            SymbolicDynamics.FullShift.FullShiftSpace 2 →
              SymbolicDynamics.FullShift.FullShiftSpace 2)
          Set.univ U n) :=
    rfl
  have hev :
      ∀ᶠ n : ℕ in Filter.atTop,
        (↑(Dynamics.coverMincard
          (id :
            SymbolicDynamics.FullShift.FullShiftSpace 2 →
              SymbolicDynamics.FullShift.FullShiftSpace 2)
          Set.univ U n) :
          ENNReal) ≤
        1 * ↑(Dynamics.coverMincard
          (id :
            SymbolicDynamics.FullShift.FullShiftSpace 2 →
              SymbolicDynamics.FullShift.FullShiftSpace 2)
          Set.univ U 1) :=
    Filter.Eventually.of_forall fun n => by
      rw [one_mul]
      exact ENat.toENNReal_le.mpr (coverMincard_id_le U n)
  have hle :
      ExpGrowth.expGrowthSup (fun n =>
        Dynamics.coverMincard
          (id :
            SymbolicDynamics.FullShift.FullShiftSpace 2 →
              SymbolicDynamics.FullShift.FullShiftSpace 2)
          Set.univ U n) ≤
        ExpGrowth.expGrowthSup (fun _ =>
          (↑(Dynamics.coverMincard
            (id :
              SymbolicDynamics.FullShift.FullShiftSpace 2 →
                SymbolicDynamics.FullShift.FullShiftSpace 2)
            Set.univ U 1) :
            ENNReal)) :=
    ExpGrowth.expGrowthSup_le_of_eventually_le
      (show (1 : ENNReal) ≠ ⊤ by simp) hev
  have hconst :
      ExpGrowth.expGrowthSup (fun _ =>
        (↑(Dynamics.coverMincard
          (id :
            SymbolicDynamics.FullShift.FullShiftSpace 2 →
              SymbolicDynamics.FullShift.FullShiftSpace 2)
          Set.univ U 1) :
          ENNReal)) =
      0 :=
    ExpGrowth.expGrowthSup_const hb_zero hb_top
  rw [hdef, ← hconst]
  exact hle

/-- The identity of the full shift has zero topological entropy. -/
theorem entropy_id_eq_zero :
    Dynamics.topologicalEntropy
        (id :
          SymbolicDynamics.FullShift.FullShiftSpace 2 →
            SymbolicDynamics.FullShift.FullShiftSpace 2) =
      0 := by
  have htop :
      Dynamics.topologicalEntropy
          (id :
            SymbolicDynamics.FullShift.FullShiftSpace 2 →
              SymbolicDynamics.FullShift.FullShiftSpace 2) =
        @Dynamics.coverEntropy
          (SymbolicDynamics.FullShift.FullShiftSpace 2)
          uniformSpaceOfCompactR1
          (id :
            SymbolicDynamics.FullShift.FullShiftSpace 2 →
              SymbolicDynamics.FullShift.FullShiftSpace 2)
          Set.univ :=
    rfl
  rw [htop]
  apply le_antisymm
  · show
        (⨆ U ∈
          @uniformity
            (SymbolicDynamics.FullShift.FullShiftSpace 2)
            uniformSpaceOfCompactR1,
          Dynamics.coverEntropyEntourage
            (id :
              SymbolicDynamics.FullShift.FullShiftSpace 2 →
                SymbolicDynamics.FullShift.FullShiftSpace 2)
            Set.univ U) ≤
        0
    apply iSup_le
    intro U
    apply iSup_le
    intro hU
    exact entourage_id_le_zero U hU
  · exact
      @Dynamics.coverEntropy_nonneg
        (SymbolicDynamics.FullShift.FullShiftSpace 2)
        Set.univ uniformSpaceOfCompactR1
        (id :
          SymbolicDynamics.FullShift.FullShiftSpace 2 →
            SymbolicDynamics.FullShift.FullShiftSpace 2)
        ⟨fun _ => (0 : Fin 2), Set.mem_univ _⟩

/-- The identity of the full shift does not have positive entropy. -/
theorem entropy_id_not_pos :
    ¬ 0 <
      Dynamics.topologicalEntropy
        (id :
          SymbolicDynamics.FullShift.FullShiftSpace 2 →
            SymbolicDynamics.FullShift.FullShiftSpace 2) := by
  rw [entropy_id_eq_zero]
  exact lt_irrefl 0

/-- The identity of the empty space has entropy `⊥`. -/
theorem entropy_empty :
    Dynamics.topologicalEntropy (id : Empty → Empty) = ⊥ := by
  have huniv : (Set.univ : Set Empty) = ∅ := by
    ext x
    exact x.elim
  have htop :
      Dynamics.topologicalEntropy (id : Empty → Empty) =
        @Dynamics.coverEntropy Empty uniformSpaceOfCompactR1
          (id : Empty → Empty) Set.univ :=
    rfl
  rw [htop, huniv]
  exact @Dynamics.coverEntropy_empty Empty _ uniformSpaceOfCompactR1

end TopologicalEntropyCompactTests
