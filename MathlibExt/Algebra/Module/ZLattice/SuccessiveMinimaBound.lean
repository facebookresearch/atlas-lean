/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Module.ZLattice.FirstAndLastMinimum
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A weak form of Minkowski's second theorem for Euclidean lattices

For a lattice `L` in a Euclidean space `E` of dimension `n`, with first minimum `λ(L)`, last
minimum `Λ(L)` and covolume `vol(L)` (`ZLattice.firstMinimum`, `ZLattice.lastMinimum`,
`ZLattice.covolume` for the Haar measure given by an orthonormal basis), this module proves

* `ZLattice.firstMinimum_pow_mul_lastMinimum_le`: `λ(L) ^ (n - 1) Λ(L) ≤ √n ^ n vol(L)`,

the second inequality of Gaudron and Rémond's Lemme 3.1 in *Polarisations et isogénies*.

The proof is direct and does not use Minkowski's theorem on successive minima. For `n > 0`, let
`V` be the span of the vectors of `L` of norm `< Λ(L)`, a proper subspace, and `k = dim V < n`.
Minkowski's convex body theorem, applied to a box with sides `2a` along an orthonormal basis of
`V` and `2b` along an orthonormal basis of its orthogonal complement, for `a < λ(L) / √n` and
`b < Λ(L) / √n`, gives `λ(L) ^ k Λ(L) ^ (n - k) ≤ √n ^ n vol(L)`; then `λ(L) ≤ Λ(L)`.
-/

@[expose] public section

open MeasureTheory Module

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The first minimum of a $\mathbb{Z}$-submodule is nonnegative. -/
theorem firstMinimum_nonneg (L : Submodule ℤ E) : 0 ≤ firstMinimum L :=
  Real.sInf_nonneg (by rintro _ ⟨x, _, rfl⟩; exact norm_nonneg x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The last minimum of a $\mathbb{Z}$-submodule is nonnegative. -/
theorem lastMinimum_nonneg (L : Submodule ℤ E) : 0 ≤ lastMinimum L :=
  Real.sInf_nonneg fun _ hr ↦ hr.1.le

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Every nonzero vector of $L$ has norm at least the first minimum $\lambda(L)$. -/
theorem firstMinimum_le_norm {L : Submodule ℤ E} {x : E} (hx : x ∈ L) (hx0 : x ≠ 0) :
    firstMinimum L ≤ ‖x‖ :=
  csInf_le ⟨0, by rintro _ ⟨y, _, rfl⟩; exact norm_nonneg y⟩ ⟨x, ⟨hx, hx0⟩, rfl⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- If $L$ contains $n = \dim E$ linearly independent vectors of norm at most $r > 0$, then
$\Lambda(L) \le r$. -/
theorem lastMinimum_le {L : Submodule ℤ E} {r : ℝ} (hr : 0 < r) (ω : Fin (finrank ℝ E) → E)
    (hω : LinearIndependent ℝ ω) (hωL : ∀ i, ω i ∈ L ∧ ‖ω i‖ ≤ r) : lastMinimum L ≤ r :=
  csInf_le ⟨0, fun _ hs ↦ hs.1.le⟩ ⟨hr, ω, hω, hωL⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- A lattice $L$ in a finite-dimensional real inner product space of positive dimension has
$\lambda(L) \le \Lambda(L)$. -/
theorem firstMinimum_le_lastMinimum (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hn : 0 < finrank ℝ E) : firstMinimum L ≤ lastMinimum L := by
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ L) = finrank ℝ E := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  set B := ((Free.chooseBasis ℤ L).reindex (Fintype.equivFinOfCardEq hcard)).ofZLatticeBasis ℝ L
  refine le_csInf ⟨1 + ∑ i, ‖B i‖,
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ ↦ norm_nonneg _), B,
    B.linearIndependent, fun i ↦ ⟨?_, ?_⟩⟩ ?_
  · rw [Module.Basis.ofZLatticeBasis_apply]
    exact Subtype.mem _
  · have := Finset.single_le_sum (f := fun i ↦ ‖B i‖) (fun i _ ↦ norm_nonneg _)
      (Finset.mem_univ i)
    linarith
  · rintro r ⟨-, ω, hω, hωL⟩
    let i₀ : Fin (finrank ℝ E) := ⟨0, hn⟩
    exact (firstMinimum_le_norm (hωL i₀).1 (hω.ne_zero i₀)).trans (hωL i₀).2

omit [MeasurableSpace E] [BorelSpace E] in
/-- In a finite-dimensional real inner product space of positive dimension, the vectors of a
$\mathbb{Z}$-submodule $L$ of norm less than $\Lambda(L)$ span a proper subspace. -/
theorem span_norm_lt_lastMinimum_ne_top (L : Submodule ℤ E) (hn : 0 < finrank ℝ E) :
    Submodule.span ℝ {x : E | x ∈ L ∧ ‖x‖ < lastMinimum L} ≠ ⊤ := by
  intro hspan
  set S := {x : E | x ∈ L ∧ ‖x‖ < lastMinimum L}
  obtain ⟨b, hbS, hbspan, hli⟩ := exists_linearIndependent ℝ S
  let B : Basis b ℝ E := Basis.mk hli (by rw [Subtype.range_coe, hbspan, hspan])
  have : Finite b := Module.Finite.finite_basis B
  have : Fintype b := Fintype.ofFinite b
  let e : Fin (finrank ℝ E) ≃ b := (Fintype.equivFinOfCardEq (finrank_eq_card_basis B).symm).symm
  set ω : Fin (finrank ℝ E) → E := fun i ↦ (e i : E)
  have hω : LinearIndependent ℝ ω := hli.comp e e.injective
  have hωS : ∀ i, ω i ∈ S := fun i ↦ hbS (e i).2
  have : Nonempty (Fin (finrank ℝ E)) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i ↦ ‖ω i‖) Finset.univ_nonempty
  have hpos : 0 < ‖ω j‖ := norm_pos_iff.mpr (hω.ne_zero j)
  have hle := lastMinimum_le hpos ω hω fun i ↦ ⟨(hωS i).1, hj i (Finset.mem_univ i)⟩
  exact absurd (hωS j).2 (not_lt.mpr hle)

/-- **A weak form of Minkowski's second theorem** (Gaudron and Rémond, Lemme 3.1, second
inequality). Let $E$ be a Euclidean space of dimension $n$ and $L \subset E$ a lattice: a
discrete $\mathbb{Z}$-submodule that spans $E$. Let $\lambda(L)$ be its first minimum,
$\Lambda(L)$ its last minimum and $\operatorname{vol}(L)$ its covolume, for the Haar measure of
$E$ given by an orthonormal basis. Then

$$\lambda(L)^{n-1}\, \Lambda(L) \le \sqrt{n}^{\,n} \operatorname{vol}(L).$$

For $n = 0$ the exponent $n - 1$ is the natural-number subtraction $0$, $\Lambda(L) = 0$, and the
inequality reads $0 \le \operatorname{vol}(L)$.

Gaudron and Rémond take this from Martinet's form of Minkowski's second theorem with the bound
$\gamma_n \le n$ for Hermite's constant. The proof here is direct: for $n > 0$, with $V$ the
span of the vectors of $L$ of norm less than $\Lambda(L)$, a proper subspace of dimension $k < n$,
Minkowski's convex body theorem for a box with half-sides $a < \lambda(L)/\sqrt n$ along an
orthonormal basis of $V$ and $b < \Lambda(L)/\sqrt n$ along an orthonormal basis of
$V^\perp$ gives $\lambda(L)^k \Lambda(L)^{n-k} \le \sqrt{n}^{\,n} \operatorname{vol}(L)$, and
$\lambda(L) \le \Lambda(L)$.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, §3, p. 2069 (the minima $\lambda$ and $\Lambda$), Lemme 3.1, second inequality,
p. 2069. -/
theorem firstMinimum_pow_mul_lastMinimum_le (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    firstMinimum L ^ (finrank ℝ E - 1) * lastMinimum L ≤
      √(finrank ℝ E : ℝ) ^ finrank ℝ E * covolume L := by
  set n := finrank ℝ E with hn_def
  set c := covolume L
  set lam := firstMinimum L
  set Lam := lastMinimum L
  have hc0 : 0 < c := covolume_pos L volume
  have hlam0 : 0 ≤ lam := firstMinimum_nonneg L
  have hLam0 : 0 ≤ Lam := lastMinimum_nonneg L
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- In dimension `0`, the empty family shows `Λ(L) ≤ vol(L)`.
    have hle : Lam ≤ c := by
      refine lastMinimum_le hc0 (fun i ↦ absurd i.2 (by omega)) ?_ fun i ↦ absurd i.2 (by omega)
      have : IsEmpty (Fin n) := by rw [hn]; exact Fin.isEmpty'
      exact linearIndependent_empty_type
    rw [hn]
    simpa using hle
  have hn0 : n ≠ 0 := hn.ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hnR
  have hlamLam : lam ≤ Lam := firstMinimum_le_lastMinimum L hn
  -- The subspace `V` spanned by the vectors of norm `< Λ(L)`, and an orthonormal basis of `E`
  -- extending one of `V`.
  set V := Submodule.span ℝ {x : E | x ∈ L ∧ ‖x‖ < Lam}
  have hVtop : V ≠ ⊤ := span_norm_lt_lastMinimum_ne_top L hn
  have hVout : ∀ x ∈ L, x ∉ V → Lam ≤ ‖x‖ := fun x hx hxV ↦
    not_lt.mp fun h ↦ hxV (Submodule.subset_span ⟨hx, h⟩)
  set bV := stdOrthonormalBasis ℝ V
  set v : Set E := Set.range fun j ↦ (bV j : E)
  have hvV : v ⊆ V := by rintro _ ⟨j, rfl⟩; exact (bV j).2
  have hvo : Orthonormal ℝ ((↑) : v → E) :=
    (bV.orthonormal.comp_linearIsometry V.subtypeₗᵢ).toSubtypeRange
  obtain ⟨u, b, hvu, hb⟩ := hvo.exists_orthonormalBasis_extension
  have hcardu : Fintype.card u = n := (finrank_eq_card_basis b.toBasis).symm
  classical
  -- `p i`: the basis vector `i` belongs to the orthonormal basis of `V`.
  set p : u → Prop := fun i ↦ (i : E) ∈ v
  set k := (Finset.univ.filter p).card with hk_def
  have hk_add : k + (Finset.univ.filter fun i ↦ ¬ p i).card = n := by
    rw [hk_def, Finset.card_filter_add_card_filter_not, Finset.card_univ, hcardu]
  -- Some basis vector lies outside `v`, so `k < n`.
  have hk_lt : k < n := by
    by_contra hkn
    have hall : ∀ i : u, p i := by
      intro i
      by_contra hi
      have hpos : 0 < (Finset.univ.filter fun i ↦ ¬ p i).card :=
        Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      omega
    apply hVtop
    rw [eq_top_iff, ← b.toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [OrthonormalBasis.coe_toBasis, hb]
    exact hvV (hall i)
  -- Coordinates in the basis `b`.
  set φ : E → (u → ℝ) := fun x ↦ (b.repr x).ofLp
  have hφ_apply : ∀ x i, φ x i = inner ℝ (i : E) x := fun x i ↦ by
    simp only [φ, OrthonormalBasis.repr_apply_apply, hb]
  have hnorm_sq : ∀ x, ‖x‖ ^ 2 = ∑ i, φ x i ^ 2 := fun x ↦ by
    rw [← b.repr.norm_map, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ by positivity)]
    simp [φ, Real.norm_eq_abs, sq_abs]
  -- A vector of `V` has zero coordinates outside `v`.
  have hcoordV : ∀ x ∈ V, ∀ i : u, ¬ p i → φ x i = 0 := by
    intro x hxV i hi
    have hexp : (∑ j, inner ℝ (bV j) (⟨x, hxV⟩ : V) • (bV j : E)) = x := by
      have := congrArg Subtype.val (bV.sum_repr' ⟨x, hxV⟩)
      simpa [Submodule.coe_sum] using this
    have ho : Orthonormal ℝ ((↑) : u → E) := hb ▸ b.orthonormal
    rw [hφ_apply, ← hexp, inner_sum]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [inner_smul_right]
    have hj : (bV j : E) ∈ (u : Set E) := hvu ⟨j, rfl⟩
    have hne : i ≠ ⟨(bV j : E), hj⟩ := fun h ↦ hi (by rw [h]; exact ⟨j, rfl⟩)
    rw [show (bV j : E) = ((⟨(bV j : E), hj⟩ : u) : E) from rfl, ho.2 hne, mul_zero]
  -- The main inequality `λ^k Λ^(n-k) ≤ √n^n vol(L)`.
  have hmain : lam ^ k * Lam ^ (n - k) ≤ √(n : ℝ) ^ n * c := by
    by_contra hlt
    push Not at hlt
    set Pk := lam ^ k * Lam ^ (n - k)
    have hP0 : 0 < Pk := lt_of_le_of_lt (by positivity) hlt
    have hLam_pos : 0 < Lam := by
      rcases hLam0.lt_or_eq with h | h
      · exact h
      · exfalso
        have : Pk = 0 := by
          simp only [Pk, ← h]
          rw [zero_pow (by omega), mul_zero]
        exact hP0.ne' this
    -- Choose `t < 1` with `t ^ n Pk > √n ^ n vol(L)`.
    set ρ := √(n : ℝ) ^ n * c / Pk
    have hρ0 : 0 ≤ ρ := by positivity
    have hρ1 : ρ < 1 := (div_lt_one hP0).mpr hlt
    set s₀ := ρ ^ ((n : ℝ)⁻¹)
    have hs₀0 : 0 ≤ s₀ := Real.rpow_nonneg hρ0 _
    have hs₀1 : s₀ < 1 := Real.rpow_lt_one hρ0 hρ1 (inv_pos.mpr hnR)
    set t := (s₀ + 1) / 2 with ht_def
    have ht0 : 0 < t := by positivity
    have ht1 : t < 1 := by rw [ht_def]; linarith
    have hts : s₀ < t := by rw [ht_def]; linarith
    have htn : ρ < t ^ n := by
      have := pow_lt_pow_left₀ hts hs₀0 hn0
      rwa [Real.rpow_inv_natCast_pow hρ0 hn0] at this
    have htP : √(n : ℝ) ^ n * c < t ^ n * Pk := by
      have := (div_lt_iff₀ hP0).mp htn
      linarith
    -- The box.
    set a := t * lam / √(n : ℝ)
    set bb := t * Lam / √(n : ℝ)
    have ha0 : 0 ≤ a := by positivity
    have hab : a ≤ bb := by
      simp only [a, bb]
      gcongr
    set r : u → ℝ := fun i ↦ if p i then a else bb
    have hr0 : ∀ i, 0 ≤ r i := fun i ↦ by simp only [r]; split_ifs <;> linarith
    have hr_le : ∀ i, r i ≤ bb := fun i ↦ by simp only [r]; split_ifs <;> linarith
    set s : Set E := φ ⁻¹' Set.Icc (fun i ↦ -r i) r
    have hφ : MeasurePreserving φ volume volume :=
      (PiLp.volume_preserving_ofLp u).comp b.measurePreserving_repr
    have hprod : ∏ i, (r i - -r i) = 2 ^ n * (a ^ k * bb ^ (n - k)) := by
      have h2 : ∀ i, r i - -r i = 2 * r i := fun i ↦ by ring
      simp only [h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcardu]
      congr 1
      simp only [r]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
      congr 2
      omega
    have hs_vol : volume s = ENNReal.ofReal (2 ^ n * (a ^ k * bb ^ (n - k))) := by
      rw [hφ.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi,
        ← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ by linarith [hr0 i]), hprod]
    have hs_symm : ∀ x ∈ s, -x ∈ s := by
      intro x hx
      simp only [s, Set.mem_preimage, Set.mem_Icc, Pi.le_def, φ, map_neg] at hx ⊢
      refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
      · have := (hx.2 i); simp only [PiLp.neg_apply] at this ⊢; linarith
      · have := (hx.1 i); simp only [PiLp.neg_apply] at this ⊢; linarith
    have hs_conv : Convex ℝ s := by
      have hlin : IsLinearMap ℝ φ :=
        ⟨fun x y ↦ by simp [φ], fun a x ↦ by simp [φ]⟩
      exact (convex_Icc _ _).is_linear_preimage hlin
    -- `a ^ k bb ^ (n - k) = t ^ n Pk / √n ^ n`.
    have hsplit : ∀ y : ℝ, y ^ n = y ^ k * y ^ (n - k) := fun y ↦ by
      rw [← pow_add, Nat.add_sub_cancel' hk_lt.le]
    have habP : a ^ k * bb ^ (n - k) = t ^ n * Pk / √(n : ℝ) ^ n := by
      rw [hsplit t, hsplit (√(n : ℝ))]
      simp only [a, bb, Pk, div_pow, mul_pow]
      field_simp
    have hbox : 2 ^ n * c < 2 ^ n * (a ^ k * bb ^ (n - k)) := by
      rw [habP]
      gcongr
      rw [lt_div_iff₀ (pow_pos hsq n)]
      linarith
    -- Minkowski's convex body theorem.
    set B := Free.chooseBasis ℤ L
    have hfund := ZLattice.isAddFundamentalDomain B volume
    have hF : volume (ZSpan.fundamentalDomain (B.ofZLatticeBasis ℝ L)) = ENNReal.ofReal c := by
      have hc := ZLattice.covolume_eq_measure_fundamentalDomain L volume hfund
      rw [measureReal_def] at hc
      rw [show c = _ from hc, ENNReal.ofReal_toReal]
      exact (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    have hlt' : volume (ZSpan.fundamentalDomain (B.ofZLatticeBasis ℝ L)) * 2 ^ finrank ℝ E <
        volume s := by
      rw [hF, hs_vol, show (2 : ENNReal) ^ finrank ℝ E = ENNReal.ofReal (2 ^ n) by
        rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat],
        ← ENNReal.ofReal_mul hc0.le,
        ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (by positivity) hbox), mul_comm]
      exact hbox
    have : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
    obtain ⟨x, hx0, hxs⟩ :=
      exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure (L := L.toAddSubgroup)
        hfund hs_symm hs_conv hlt'
    have hxL : (x : E) ∈ L := x.2
    have hx0' : (x : E) ≠ 0 := fun h ↦ hx0 (Subtype.ext h)
    have hcoord : ∀ i, φ x i ^ 2 ≤ r i ^ 2 := fun i ↦ by
      have h1 := hxs.1 i
      have h2 := hxs.2 i
      simp only at h1 h2
      nlinarith [hr0 i]
    by_cases hxV : (x : E) ∈ V
    · -- Then `‖x‖ ≤ √n a = t λ`, against `λ ≤ ‖x‖`.
      have hsum : ‖(x : E)‖ ^ 2 ≤ n * a ^ 2 := by
        rw [hnorm_sq]
        calc ∑ i, φ x i ^ 2 ≤ ∑ _i : u, a ^ 2 := by
              refine Finset.sum_le_sum fun i _ ↦ ?_
              by_cases hi : p i
              · have := hcoord i
                rwa [show r i = a by simp [r, hi]] at this
              · rw [hcoordV x hxV i hi, zero_pow two_ne_zero]; positivity
          _ = n * a ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, hcardu, nsmul_eq_mul]
      have hna : n * a ^ 2 = (t * lam) ^ 2 := by
        simp only [a, div_pow, Real.sq_sqrt hnR.le]
        field_simp
      have hxle : ‖(x : E)‖ ≤ t * lam :=
        (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp
          (hsum.trans hna.le)
      have hlamx := firstMinimum_le_norm hxL hx0'
      have hlam_zero : lam = 0 := by nlinarith
      have : ‖(x : E)‖ ≤ 0 := by rw [hlam_zero, mul_zero] at hxle; exact hxle
      exact hx0' (norm_le_zero_iff.mp this)
    · -- Then `‖x‖ ≤ √n bb = t Λ < Λ`, against `Λ ≤ ‖x‖`.
      have hsum : ‖(x : E)‖ ^ 2 ≤ n * bb ^ 2 := by
        rw [hnorm_sq]
        calc ∑ i, φ x i ^ 2 ≤ ∑ _i : u, bb ^ 2 := by
              refine Finset.sum_le_sum fun i _ ↦ (hcoord i).trans ?_
              exact pow_le_pow_left₀ (hr0 i) (hr_le i) 2
          _ = n * bb ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, hcardu, nsmul_eq_mul]
      have hnb : n * bb ^ 2 = (t * Lam) ^ 2 := by
        simp only [bb, div_pow, Real.sq_sqrt hnR.le]
        field_simp
      have hxle : ‖(x : E)‖ ≤ t * Lam :=
        (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp
          (hsum.trans hnb.le)
      have hLamx := hVout _ hxL hxV
      nlinarith
  -- Conclusion, from `λ ≤ Λ` and `k ≤ n - 1`.
  have hk1 : k ≤ n - 1 := by omega
  calc lam ^ (n - 1) * Lam = lam ^ k * (lam ^ (n - 1 - k) * Lam) := by
        rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hk1]
    _ ≤ lam ^ k * (Lam ^ (n - 1 - k) * Lam) := by gcongr
    _ = lam ^ k * Lam ^ (n - k) := by
        rw [← pow_succ]
        congr 2
        omega
    _ ≤ √(n : ℝ) ^ n * c := hmain

end ZLattice
