/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fintype.Pi
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

public import MathlibExt.Topology.MetricSpace.LipschitzParametrizable

/-!
# Lipschitz images meet few integer unit cubes (ATLAS N385, Lemma 19.5 slice)

Clean-room formalization of one reusable slice of ATLAS `NumberTheoryI` N385
(Lemma 19.5), extracted from the exact source
[`v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean`, lines 84–311](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean#L84-L311).

This module provides only the single-parametrization cube-count ingredients used
later to bound boundary cubes: the floor-difference estimate, the
scaled-coordinate estimate, the finite-grid injection, finiteness of the
integer-cube set, the explicit finite-grid cardinality estimate, and the real
`O(t ^ d)` consequence. It does not claim the full measurable-set
lattice-point asymptotic of N385.

The parametrization domain is the subtype `↥(unitCube d)` from the merged N384
API (`MathlibExt.Topology.MetricSpace.LipschitzParametrizable`), so every grid
representative below itself carries a proof that each coordinate lies in
`[0, 1]`. Integer unit cubes use the half-open convention `[vᵢ, vᵢ + 1)` in
each coordinate (see `mem_integerCubeSet_iff`).

Main declarations:

- `LipschitzImageCubeCount.integerCubeSet`: the set of integer vectors `v`
  whose half-open unit cube meets `t • f (unitCube d)`.
- `LipschitzImageCubeCount.mem_integerCubeSet_iff`: unfolding lemma.
- `LipschitzImageCubeCount.abs_floor_sub_le_ceil`: if `|a - b| ≤ D` then
  `|⌊a⌋ - ⌊b⌋| ≤ ⌈D⌉` (source lines 85–95).
- `LipschitzImageCubeCount.scaled_coord_abs_le`: Lipschitz control plus
  `dist y y' ≤ 1 / T` gives `|t * f y i - t * f y' i| ≤ K` (source lines
  97–112).
- `LipschitzImageCubeCount.finite_integerCubeSet`: finiteness for `t ≥ 1`.
- `LipschitzImageCubeCount.card_integerCubeSet_le`: the explicit estimate
  `Nat.card ≤ ⌈t⌉₊ ^ d * (2 * ⌈K * √d⌉₊ + 3) ^ n` (source lines 114–222).
- `LipschitzImageCubeCount.exists_cubeCount_le_const_mul_pow`: the real
  `C * t ^ d` consequence with `C` independent of `t` (source lines 283–311).
-/

@[expose] public section

open scoped NNReal

namespace LipschitzImageCubeCount

/-- **Integer cube set.** Let $f$ be a map from the unit cube $[0, 1]^d$ to $\mathbb{R}^n$ and let
$t$ be a real number. The integer cube set of $f$ at scale $t$ is the set of integer vectors
$v \in \mathbb{Z}^n$ for which some point $y$ of the unit cube satisfies
$v_i \le t f(y)_i < v_i + 1$ for every coordinate $i$, that is, the set of integer vectors whose
half-open unit cube $\prod_i [v_i, v_i + 1)$ meets the dilate $t \cdot f([0, 1]^d)$. -/
def integerCubeSet {n d : ℕ} (f : ↥(unitCube d) → (Fin n → ℝ)) (t : ℝ) :
    Set (Fin n → ℤ) :=
  {v | ∃ y : ↥(unitCube d),
    ∀ i, (v i : ℝ) ≤ t * (f y) i ∧ t * (f y) i < (v i : ℝ) + 1}

/-- **Membership in the integer cube set.** Let $f$ be a map from the unit cube $[0, 1]^d$ to
$\mathbb{R}^n$, let $t$ be a real number and let $v \in \mathbb{Z}^n$. Then $v$ belongs to the
integer cube set of $f$ at scale $t$ if and only if some point $y$ of the unit cube satisfies
$v_i \le t f(y)_i < v_i + 1$ for every coordinate $i$. -/
theorem mem_integerCubeSet_iff {n d : ℕ} {f : ↥(unitCube d) → (Fin n → ℝ)}
    {t : ℝ} {v : Fin n → ℤ} :
    v ∈ integerCubeSet f t ↔ ∃ y : ↥(unitCube d),
      ∀ i, (v i : ℝ) ≤ t * (f y) i ∧ t * (f y) i < (v i : ℝ) + 1 :=
  Iff.rfl

/-- **Floor differences are bounded by a ceiling.** For real numbers $a$, $b$ and $D$ with
$|a - b| \le D$, the integers $\lfloor a \rfloor$ and $\lfloor b \rfloor$ satisfy
$|\lfloor a \rfloor - \lfloor b \rfloor| \le \lceil D \rceil$.

Source: v1 AnalyticClassNumber.lean, lines 85–95. -/
theorem abs_floor_sub_le_ceil {a b D : ℝ} (hab : |a - b| ≤ D) :
    |⌊a⌋ - ⌊b⌋| ≤ ⌈D⌉ := by
  rw [abs_le]
  have hab' := abs_le.mp hab
  constructor
  · suffices h : ⌊b⌋ - ⌊a⌋ ≤ ⌈D⌉ by omega
    have h1 : ⌊b⌋ ≤ ⌊a + D⌋ :=
      Int.floor_le_floor (by linarith [hab'.1])
    have h2 : ⌊a + D⌋ < ⌊a⌋ + ⌈D⌉ + 1 := by
      rw [Int.floor_lt]
      push_cast
      linarith [Int.lt_floor_add_one a, Int.le_ceil D]
    omega
  · suffices h : ⌊a⌋ - ⌊b⌋ ≤ ⌈D⌉ by omega
    have h1 : ⌊a⌋ ≤ ⌊b + D⌋ :=
      Int.floor_le_floor (by linarith [hab'.2])
    have h2 : ⌊b + D⌋ < ⌊b⌋ + ⌈D⌉ + 1 := by
      rw [Int.floor_lt]
      push_cast
      linarith [Int.lt_floor_add_one b, Int.le_ceil D]
    omega

/-- **Dilated Lipschitz maps vary by at most $K$ on cells of size $1/T$.** Let $K \ge 0$, let $f$
be a $K$-Lipschitz map from the unit cube $[0, 1]^d$ to $\mathbb{R}^n$, both carrying the sup
distance, and let $t$ and $T$ be real numbers with $0 < t \le T$. If $y$ and $y'$ are points of
the unit cube at distance at most $1/T$, then $|t f(y)_i - t f(y')_i| \le K$ for every coordinate
$i$.

Source: v1 AnalyticClassNumber.lean, lines 97–112. -/
theorem scaled_coord_abs_le {n d : ℕ} {f : ↥(unitCube d) → (Fin n → ℝ)}
    {K : ℝ≥0} (hf : LipschitzWith K f) {y y' : ↥(unitCube d)}
    {t T : ℝ} (ht_pos : 0 < t) (hT_pos : 0 < T) (ht_le : t ≤ T)
    (hdist : dist y y' ≤ 1 / T) (i : Fin n) :
    |t * (f y) i - t * (f y') i| ≤ (K : ℝ) := by
  have h1 : |(f y) i - (f y') i| ≤ (K : ℝ) * (1 / T) := by
    calc |(f y) i - (f y') i|
        = dist ((f y) i) ((f y') i) := (Real.dist_eq _ _).symm
      _ ≤ dist (f y) (f y') := dist_le_pi_dist (f y) (f y') i
      _ ≤ (K : ℝ) * dist y y' := hf.dist_le_mul y y'
      _ ≤ (K : ℝ) * (1 / T) :=
          mul_le_mul_of_nonneg_left hdist K.coe_nonneg
  rw [show t * (f y) i - t * (f y') i = t * ((f y) i - (f y') i) by ring,
    abs_mul, abs_of_pos ht_pos]
  calc t * |(f y) i - (f y') i|
      ≤ t * ((K : ℝ) * (1 / T)) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt ht_pos)
    _ = (K : ℝ) * (t / T) := by ring
    _ ≤ (K : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left
          (div_le_one_of_le₀ ht_le (le_of_lt hT_pos)) K.coe_nonneg
    _ = (K : ℝ) := by ring

/-- **Counting integer cubes met by a dilated Lipschitz image.** Let $d$ and $n$ be natural
numbers, let $K \ge 0$, and let $f$ be a $K$-Lipschitz map from the unit cube $[0, 1]^d$ to
$\mathbb{R}^n$, both carrying the sup distance. For every real $t \ge 1$, the cardinality of the
integer cube set of $f$ at scale $t$, taken as a natural number, is at most
$\lceil t \rceil^d \, (2 \lceil K \sqrt{d} \rceil + 3)^n$.

The proof puts $T = \lceil t \rceil$, partitions the cube into $T^d$ cells with lower-corner
representatives, bounds every floor-coordinate offset from the representative by
$L = \lceil K \sqrt{d} \rceil$, and encodes each met integer cube injectively by its cell and an
offset in $\{0, \dots, 2L + 2\}^n$.

Source: v1 AnalyticClassNumber.lean, lines 114–222. -/
theorem card_integerCubeSet_le {n d : ℕ} (f : ↥(unitCube d) → (Fin n → ℝ))
    (K : ℝ≥0) (hf : LipschitzWith K f) (t : ℝ) (ht : 1 ≤ t) :
    Nat.card (integerCubeSet f t) ≤
      ⌈t⌉₊ ^ d * (2 * ⌈(K : ℝ) * Real.sqrt d⌉₊ + 3) ^ n := by
  set T : ℕ := ⌈t⌉₊
  set L : ℕ := ⌈(K : ℝ) * Real.sqrt d⌉₊
  set M : ℕ := 2 * L + 3
  have hT_pos : 0 < T := Nat.ceil_pos.mpr (by linarith)
  have hT' : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT_pos
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hT'
  have ht_pos : (0 : ℝ) < t := by linarith
  have ht_le_T : t ≤ (T : ℝ) := Nat.le_ceil t
  let cube_idx : ↥(unitCube d) → (Fin d → Fin T) :=
    fun y j => ⟨min (⌊(T : ℝ) * y.val j⌋₊) (T - 1), by omega⟩
  -- Lower-corner representative of a grid cell. The anonymous-constructor
  -- proof is the required evidence that each coordinate lies in `[0, 1]`.
  let y₀ : (Fin d → Fin T) → ↥(unitCube d) := fun c =>
    ⟨fun j => ((c j : ℕ) : ℝ) / (T : ℝ), by
      change _ ∈ Set.Icc (0 : Fin d → ℝ) 1
      refine Set.mem_Icc.mpr ⟨?_, ?_⟩ <;> intro j
      · change (0 : ℝ) ≤ ((c j : ℕ) : ℝ) / (T : ℝ)
        exact div_nonneg (Nat.cast_nonneg _) hT'.le
      · change ((c j : ℕ) : ℝ) / (T : ℝ) ≤ 1
        have hlt : ((c j : ℕ) : ℝ) ≤ (T : ℝ) := by
          exact_mod_cast le_of_lt (c j).isLt
        exact div_le_one_of_le₀ hlt hT'.le⟩
  let ref_vec : (Fin d → Fin T) → (Fin n → ℤ) :=
    fun c i => ⌊t * f (y₀ c) i⌋
  have dist_bound : ∀ y : ↥(unitCube d),
      dist y (y₀ (cube_idx y)) ≤ 1 / (T : ℝ) := by
    intro y
    rw [Subtype.dist_eq, dist_pi_le_iff (by positivity)]
    intro j
    have hmem : (0 : Fin d → ℝ) ≤ y.val ∧ y.val ≤ 1 :=
      Set.mem_Icc.mp y.property
    have hyj0 : 0 ≤ y.val j := hmem.1 j
    have hyj1 : y.val j ≤ 1 := hmem.2 j
    change dist (y.val j) ((y₀ (cube_idx y)).val j) ≤ 1 / (T : ℝ)
    set c : ℕ := min (⌊(T : ℝ) * y.val j⌋₊) (T - 1)
    have hval : (y₀ (cube_idx y)).val j = (c : ℝ) / (T : ℝ) := rfl
    rw [hval]
    have hfl : (⌊(T : ℝ) * y.val j⌋₊ : ℝ) ≤ (T : ℝ) * y.val j :=
      Nat.floor_le (mul_nonneg hT'.le hyj0)
    have hfl_lt : (T : ℝ) * y.val j < (⌊(T : ℝ) * y.val j⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hc_le_fl : (c : ℝ) ≤ (⌊(T : ℝ) * y.val j⌋₊ : ℝ) := by
      exact_mod_cast Nat.min_le_left _ _
    have hc_le : (c : ℝ) ≤ (T : ℝ) * y.val j := le_trans hc_le_fl hfl
    rw [Real.dist_eq,
      show y.val j - (c : ℝ) / (T : ℝ)
        = ((T : ℝ) * y.val j - (c : ℝ)) / (T : ℝ) by field_simp,
      abs_div, abs_of_pos hT', abs_of_nonneg (by linarith)]
    apply (div_le_div_iff_of_pos_right hT').mpr
    by_cases hle : ⌊(T : ℝ) * y.val j⌋₊ ≤ T - 1
    · have hc_eq : c = ⌊(T : ℝ) * y.val j⌋₊ := Nat.min_eq_left hle
      rw [hc_eq]; linarith
    · have hc_eq : c = T - 1 := Nat.min_eq_right (by omega)
      rw [hc_eq]
      have hT1 : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ T)]; simp
      rw [hT1]
      linarith [mul_le_mul_of_nonneg_left hyj1 (le_of_lt hT')]
  have offset_bound : ∀ y : ↥(unitCube d), ∀ i : Fin n,
      |⌊t * (f y) i⌋ - ref_vec (cube_idx y) i| ≤ (L : ℤ) := by
    intro y i
    by_cases hd : d = 0
    · subst hd
      have heq_y : y = y₀ (cube_idx y) := by
        apply Subtype.ext
        funext j
        exact j.elim0
      change |⌊t * f y i⌋ - ⌊t * f (y₀ (cube_idx y)) i⌋| ≤ (L : ℤ)
      have hfeq : f y = f (y₀ (cube_idx y)) := congrArg f heq_y
      rw [hfeq, sub_self, abs_zero]
      exact_mod_cast Nat.zero_le L
    · have hdist := dist_bound y
      have hcoord := scaled_coord_abs_le hf ht_pos hT' ht_le_T hdist i
      change |⌊t * f y i⌋ - ⌊t * f (y₀ (cube_idx y)) i⌋| ≤ (L : ℤ)
      calc |⌊t * f y i⌋ - ⌊t * f (y₀ (cube_idx y)) i⌋|
          ≤ ⌈(K : ℝ)⌉ := abs_floor_sub_le_ceil hcoord
        _ ≤ (L : ℤ) := by
            have h_nonneg : 0 ≤ (K : ℝ) * Real.sqrt d :=
              mul_nonneg K.coe_nonneg (Real.sqrt_nonneg _)
            rw [show (L : ℤ) = ⌈(K : ℝ) * Real.sqrt d⌉ from by
              rw [show (L : ℤ) = (⌈(K : ℝ) * Real.sqrt d⌉₊ : ℤ) from rfl]
              exact_mod_cast (Int.toNat_of_nonneg (Int.ceil_nonneg h_nonneg))]
            exact Int.ceil_le_ceil (le_mul_of_one_le_right K.coe_nonneg
              (by rw [← Real.sqrt_one]
                  exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ d by omega))))
  let choose_y : ↥(integerCubeSet f t) → ↥(unitCube d) :=
    fun sv => (mem_integerCubeSet_iff.mp sv.property).choose
  have choose_prop : ∀ (sv : ↥(integerCubeSet f t)) (i : Fin n),
      (sv.val i : ℝ) ≤ t * (f (choose_y sv)) i ∧
      t * (f (choose_y sv)) i < (sv.val i : ℝ) + 1 :=
    fun sv i => (mem_integerCubeSet_iff.mp sv.property).choose_spec i
  have v_eq : ∀ (sv : ↥(integerCubeSet f t)) (i : Fin n),
      sv.val i = ⌊t * (f (choose_y sv)) i⌋ := by
    intro sv i
    exact (Int.floor_eq_iff.mpr ⟨(choose_prop sv i).1, (choose_prop sv i).2⟩).symm
  have off_in_range : ∀ (sv : ↥(integerCubeSet f t)) (i : Fin n),
      0 ≤ sv.val i - ref_vec (cube_idx (choose_y sv)) i + (L : ℤ) + 1 ∧
      (sv.val i - ref_vec (cube_idx (choose_y sv)) i + (L : ℤ) + 1).toNat < M := by
    intro sv i
    rw [v_eq sv i]
    have hoff' := abs_le.mp (offset_bound (choose_y sv) i)
    exact ⟨by omega, by rw [Int.toNat_lt (by omega)]; omega⟩
  let φ : ↥(integerCubeSet f t) → (Fin d → Fin T) × (Fin n → Fin M) := fun sv =>
    (cube_idx (choose_y sv),
     fun i => ⟨(sv.val i - ref_vec (cube_idx (choose_y sv)) i + (L : ℤ) + 1).toNat,
       (off_in_range sv i).2⟩)
  have hφ_inj : Function.Injective φ := by
    intro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ heq
    have heq1 : cube_idx (choose_y ⟨v₁, hv₁⟩) = cube_idx (choose_y ⟨v₂, hv₂⟩) :=
      congrArg Prod.fst heq
    have heq_snd := congrArg Prod.snd heq
    have heq_i := congrFun heq_snd
    ext i
    change v₁ i = v₂ i
    have h1 : 0 ≤ v₁ i - ref_vec (cube_idx (choose_y ⟨v₁, hv₁⟩)) i + (L : ℤ) + 1 :=
      (off_in_range ⟨v₁, hv₁⟩ i).1
    have h2 : 0 ≤ v₂ i - ref_vec (cube_idx (choose_y ⟨v₂, hv₂⟩)) i + (L : ℤ) + 1 :=
      (off_in_range ⟨v₂, hv₂⟩ i).1
    have hcast : ((v₁ i - ref_vec (cube_idx (choose_y ⟨v₁, hv₁⟩)) i
        + (L : ℤ) + 1).toNat : ℤ) =
        ((v₂ i - ref_vec (cube_idx (choose_y ⟨v₂, hv₂⟩)) i
        + (L : ℤ) + 1).toNat : ℤ) :=
      congrArg (fun z : Fin M => ((z.val : ℕ) : ℤ)) (heq_i i)
    rw [heq1] at hcast h1
    rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at hcast
    omega
  calc Nat.card (integerCubeSet f t)
      ≤ Nat.card ((Fin d → Fin T) × (Fin n → Fin M)) :=
        Nat.card_le_card_of_injective φ hφ_inj
    _ = T ^ d * M ^ n := by
        rw [Nat.card_prod, Nat.card_pi, Nat.card_pi, Finset.prod_const,
          Finset.prod_const]
        simp

/-- **Dilated Lipschitz images meet finitely many integer cubes.** Let $d$ and $n$ be natural
numbers, let $K \ge 0$, and let $f$ be a $K$-Lipschitz map from the unit cube $[0, 1]^d$ to
$\mathbb{R}^n$, both carrying the sup distance. For every real $t \ge 1$, the integer cube set of
$f$ at scale $t$ is finite.

The image of $f$ is bounded, since each coordinate of $f(y)$ differs from the corresponding
coordinate of $f(0)$ by at most $K \sqrt{d}$, so every met cube index lies in an explicit
finite box. -/
theorem finite_integerCubeSet {n d : ℕ} (f : ↥(unitCube d) → (Fin n → ℝ))
    (K : ℝ≥0) (hf : LipschitzWith K f) (t : ℝ) (ht : 1 ≤ t) :
    (integerCubeSet f t).Finite := by
  have ht_pos : (0 : ℝ) < t := by linarith
  let y₀ : ↥(unitCube d) := ⟨0, unitCube_zero_mem d⟩
  have hcoord_bound : ∀ y : ↥(unitCube d), ∀ i : Fin n,
      |(f y) i - (f y₀) i| ≤ (K : ℝ) * Real.sqrt d := by
    intro y i
    calc |(f y) i - (f y₀) i|
        = dist ((f y) i) ((f y₀) i) := (Real.dist_eq _ _).symm
      _ ≤ dist (f y) (f y₀) := dist_le_pi_dist (f y) (f y₀) i
      _ ≤ (K : ℝ) * dist y y₀ := hf.dist_le_mul y y₀
      _ ≤ (K : ℝ) * Real.sqrt d := by
        apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
        rw [Subtype.dist_eq, dist_pi_le_iff (Real.sqrt_nonneg d)]
        intro j
        have hmem : (0 : Fin d → ℝ) ≤ y.val ∧ y.val ≤ 1 :=
          Set.mem_Icc.mp y.property
        have hyj0 : 0 ≤ y.val j := hmem.1 j
        have hyj1 : y.val j ≤ 1 := hmem.2 j
        change dist (y.val j) 0 ≤ Real.sqrt d
        simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hyj0]
        calc y.val j ≤ 1 := hyj1
          _ ≤ Real.sqrt d := by
            rcases Nat.eq_zero_or_pos d with hd | hd
            · subst hd; exact j.elim0
            · rw [← Real.sqrt_one]
              exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
  set R : ℝ := (∑ i, |(f y₀) i|) + (K : ℝ) * Real.sqrt d with hR
  have hfy_bound : ∀ y : ↥(unitCube d), ∀ i : Fin n, |(f y) i| ≤ R := by
    intro y i
    have h1 := hcoord_bound y i
    have h2 : |(f y₀) i| ≤ ∑ j, |(f y₀) j| := by
      refine Finset.single_le_sum (fun j _ => abs_nonneg ((f y₀) j))
        (Finset.mem_univ i)
    calc |(f y) i| = |((f y) i - (f y₀) i) + (f y₀) i| := by congr 1; ring
      _ ≤ |(f y) i - (f y₀) i| + |(f y₀) i| := abs_add_le _ _
      _ ≤ (K : ℝ) * Real.sqrt d + ∑ j, |(f y₀) j| := add_le_add h1 h2
      _ = R := by rw [hR]; ring
  set B : ℤ := ⌈t * R⌉ + 1
  apply (Set.Finite.pi' (fun _ => Set.finite_Icc (-B) B)).subset
  intro v hv i
  obtain ⟨y, hvy⟩ := mem_integerCubeSet_iff.mp hv
  have hv_eq : v i = ⌊t * (f y) i⌋ :=
    (Int.floor_eq_iff.mpr ⟨(hvy i).1, (hvy i).2⟩).symm
  have htf_bound : |t * (f y) i| ≤ t * R := by
    rw [abs_mul, abs_of_pos ht_pos]
    exact mul_le_mul_of_nonneg_left (hfy_bound y i) (le_of_lt ht_pos)
  rw [hv_eq]
  constructor
  · have h := (abs_le.mp htf_bound).1
    have hfloor := Int.floor_le_floor h
    rw [Int.floor_neg] at hfloor
    omega
  · have h := (abs_le.mp htf_bound).2
    calc ⌊t * (f y) i⌋ ≤ ⌈t * (f y) i⌉ := Int.floor_le_ceil _
      _ ≤ ⌈t * R⌉ := Int.ceil_le_ceil h
      _ ≤ B := by omega

/-- **Dilated Lipschitz images meet $O(t^d)$ integer cubes.** Let $d$ and $n$ be natural numbers,
let $K \ge 0$, and let $f$ be a $K$-Lipschitz map from the unit cube $[0, 1]^d$ to $\mathbb{R}^n$,
both carrying the sup distance. Then there is a real number $C > 0$ such that for every real
$t \ge 1$, the cardinality of the integer cube set of $f$ at scale $t$, taken as a natural number,
is at most $C t^d$.

The proof takes $C = 2^d M^n$ with $M = 2 \lceil K \sqrt{d} \rceil + 3$, which depends on $f$ only
through $K$, and on $n$ and $d$, but not on $t$; it uses $\lceil t \rceil \le 2t$ for $t \ge 1$.

Source: v1 AnalyticClassNumber.lean, lines 283–311. -/
theorem exists_cubeCount_le_const_mul_pow {n d : ℕ}
    (f : ↥(unitCube d) → (Fin n → ℝ)) (K : ℝ≥0) (hf : LipschitzWith K f) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      (Nat.card (integerCubeSet f t) : ℝ) ≤ C * t ^ d := by
  set M : ℕ := 2 * ⌈(K : ℝ) * Real.sqrt d⌉₊ + 3
  refine ⟨(2 : ℝ) ^ d * (M : ℝ) ^ n, ?_, ?_⟩
  · apply mul_pos
    · positivity
    · exact pow_pos (by positivity) n
  · intro t ht
    have hbound := card_integerCubeSet_le f K hf t ht
    have ht0 : (0 : ℝ) ≤ t := by linarith
    have hceil_le : (⌈t⌉₊ : ℝ) ≤ 2 * t := by
      have h1 : ⌈t⌉₊ ≤ ⌊t⌋₊ + 1 := Nat.ceil_le_floor_add_one t
      have h2 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
      calc (⌈t⌉₊ : ℝ) ≤ (⌊t⌋₊ + 1 : ℕ) := by exact_mod_cast h1
        _ = (⌊t⌋₊ : ℝ) + 1 := by push_cast; ring
        _ ≤ t + 1 := by linarith
        _ ≤ 2 * t := by linarith
    calc (Nat.card (integerCubeSet f t) : ℝ)
        ≤ ((⌈t⌉₊ ^ d * M ^ n : ℕ) : ℝ) := by exact_mod_cast hbound
      _ = (⌈t⌉₊ : ℝ) ^ d * (M : ℝ) ^ n := by push_cast; ring
      _ ≤ (2 * t) ^ d * (M : ℝ) ^ n := by
          apply mul_le_mul_of_nonneg_right
          · exact pow_le_pow_left₀ (by positivity) hceil_le d
          · positivity
      _ = (2 : ℝ) ^ d * (M : ℝ) ^ n * t ^ d := by ring

end LipschitzImageCubeCount
