/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant

/-!
# The first and the last minimum of a lattice in a Euclidean space

For a lattice `L` in a finite-dimensional real inner product space `E` of dimension `n`, this
module defines the first minimum `ZLattice.firstMinimum L`, the infimum of the norms of the
nonzero vectors of `L`, and the last minimum `ZLattice.lastMinimum L`, the infimum of the `r > 0`
such that `L` contains `n` linearly independent vectors of norm at most `r`. In positive dimension
both infima are attained, so they are the least such values. In dimension `0` both values are `0`
and neither is attained. It proves two bounds of Gaudron and Rémond's
*Polarisations et isogénies*, §3, with `vol(L)` the covolume `ZLattice.covolume L` for the volume
of `E`, the Haar measure that gives an orthonormal basis's parallelepiped volume `1`:

* `ZLattice.firstMinimum_le_sqrt_finrank_mul_covolume_rpow`:
  `λ(L) ≤ √n · vol(L) ^ (1 / n)`, the first inequality of their Lemme 3.1, proved from
  Minkowski's convex body theorem applied to a cube;
* `ZLattice.covolume_le_lastMinimum_pow`: `vol(L) ≤ Λ(L) ^ n`, from Hadamard's determinant
  inequality, through `ZLattice.covolume_le_prod_norm`: the covolume is at most the product of
  the norms of any `n` linearly independent vectors of `L`.
-/

@[expose] public section

open MeasureTheory Module

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The **first minimum** $\lambda(L)$ of a $\mathbb{Z}$-submodule $L$ of a real inner product
space $E$: the infimum of the norms $|x|$ of the nonzero vectors $x \in L$,
$$\lambda(L) = \inf\{|x| : x \in L \setminus \{0\}\}.$$
For a lattice in a space of positive dimension the infimum is attained, so it is the minimum
$\min\{|x| : x \in L \setminus \{0\}\}$. When $L = 0$, for instance in dimension $0$, the set is
empty and the value is $0$, which is not attained.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, §3, p. 2069. -/
noncomputable def firstMinimum (L : Submodule ℤ E) : ℝ :=
  sInf ((fun x : E ↦ ‖x‖) '' {x | x ∈ L ∧ x ≠ 0})

/-- The **last minimum** $\Lambda(L)$ of a $\mathbb{Z}$-submodule $L$ of a real inner product
space $E$ of dimension $n$: the infimum of the real numbers $r > 0$ for which there is a linearly
independent family $(\omega_1, \dots, \omega_n)$ of elements of $L$ with $|\omega_i| \le r$ for
all $i$. For a lattice in a space of positive dimension the infimum is attained, so it is the
minimum of these numbers. In dimension $0$ the empty family qualifies for every $r > 0$, so the
admissible numbers are all $r > 0$ and the value is $0$, which is not attained. If $L$ contains no
$n$ linearly independent vectors, the set is empty and the value is $0$.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, §3, p. 2069. -/
noncomputable def lastMinimum (L : Submodule ℤ E) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ ∃ ω : Fin (finrank ℝ E) → E,
    LinearIndependent ℝ ω ∧ ∀ i, ω i ∈ L ∧ ‖ω i‖ ≤ r}

/-- The covolume of a lattice $L$ in a Euclidean space $E$ of dimension $n$, for the Haar measure
given by an orthonormal basis, is at most $|\omega_1| \cdots |\omega_n|$ for every linearly
independent family $(\omega_1, \dots, \omega_n)$ of elements of $L$.

The sublattice $L'$ that the $\omega_i$ span has finite index in $L$, so
$\operatorname{vol}(L) \le \operatorname{vol}(L') = |\det(\omega_1, \dots, \omega_n)|$ in an
orthonormal basis, which Hadamard's inequality bounds by $\prod_i |\omega_i|$.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, §3, p. 2069. -/
theorem covolume_le_prod_norm (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (ω : Fin (finrank ℝ E) → E) (hω : LinearIndependent ℝ ω) (hωL : ∀ i, ω i ∈ L) :
    covolume L ≤ ∏ i, ‖ω i‖ := by
  set ob := stdOrthonormalBasis ℝ E
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ L) = finrank ℝ E := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  set b := (Free.chooseBasis ℤ L).reindex (Fintype.equivFinOfCardEq hcard)
  set B := b.ofZLatticeBasis ℝ L
  -- The covolume is `|det B|` in the orthonormal basis.
  have hvol : volume.real (ZSpan.fundamentalDomain ob.toBasis) = 1 := by
    rw [measureReal_def, measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _),
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped, ENNReal.toReal_one]
  have hcov : covolume L = |ob.toBasis.det B| := by
    rw [covolume_eq_det_mul_measureReal L volume b ob.toBasis, hvol, mul_one]
    congr 2
    ext i
    simp [B, Module.Basis.ofZLatticeBasis_apply]
  -- `det_ob ω = det_ob B * det_B ω`, and `det_B ω` is a nonzero integer.
  let M : Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℤ := fun i j ↦ b.repr ⟨ω j, hωL j⟩ i
  have hBM : B.toMatrix ω = (Int.castRingHom ℝ).mapMatrix M := by
    ext i j
    rw [Module.Basis.toMatrix_apply]
    have := Module.Basis.ofZLatticeBasis_repr_apply ℝ L b ⟨ω j, hωL j⟩ i
    exact this
  have hdetB : B.det ω = (M.det : ℝ) := by
    rw [Module.Basis.det_apply, hBM, ← RingHom.map_det]
    rfl
  have hM : M.det ≠ 0 := by
    intro h0
    have : Nonempty (Fin (finrank ℝ E)) := by
      rcases isEmpty_or_nonempty (Fin (finrank ℝ E)) with hn | hn
      · exfalso
        have : B.det ω = 1 := by
          rw [Module.Basis.det_apply]
          exact Matrix.det_isEmpty
        rw [hdetB, h0, Int.cast_zero] at this
        exact zero_ne_one this
      · exact hn
    have hu := Module.Basis.isUnit_det B
      (basisOfLinearIndependentOfCardEqFinrank hω (Fintype.card_fin _))
    rw [coe_basisOfLinearIndependentOfCardEqFinrank, hdetB, h0, Int.cast_zero] at hu
    exact not_isUnit_zero hu
  have hmul : ob.toBasis.det ω = ob.toBasis.det B * B.det ω := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply,
      ← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix]
  have hcov_le : covolume L ≤ |ob.toBasis.det ω| := by
    rw [hcov, hmul, abs_mul, hdetB]
    have h1 : (1 : ℝ) ≤ |(M.det : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hM
    nlinarith [abs_nonneg (ob.toBasis.det B)]
  -- Hadamard's inequality for the matrix whose rows are the coordinates of the `ω i`.
  set A : Matrix (Fin (finrank ℝ E)) (Fin (finrank ℝ E)) ℝ := (ob.toBasis.toMatrix ω).transpose
  have hA : ∀ i j, A i j = (ob.repr (ω i)).ofLp j := by
    intro i j
    simp [A, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
  have hdetA : ob.toBasis.det ω = A.det := by
    rw [Module.Basis.det_apply, Matrix.det_transpose]
  have hhad := MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant.hadamard_determinant_inequality
    (Complex.ofRealHom.mapMatrix A)
  rw [← RingHom.map_det] at hhad
  have hrow : ∀ i, √(∑ j, Complex.normSq ((Complex.ofRealHom.mapMatrix A) i j)) = ‖ω i‖ := by
    intro i
    rw [← ob.repr.norm_map, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [RingHom.mapMatrix_apply, Complex.normSq_ofReal, hA, sq]
  simp only [hrow] at hhad
  have hnorm : ‖Complex.ofRealHom A.det‖ = |A.det| := by
    simp [Complex.ofRealHom_eq_coe, Complex.norm_real]
  rw [hnorm] at hhad
  rw [hdetA] at hcov_le
  exact hcov_le.trans hhad

/-- **The covolume of a lattice is at most a power of its last minimum.** Let $L$ be a lattice in
a Euclidean space $E$ of dimension $n$: a discrete $\mathbb{Z}$-submodule that spans $E$. Let
$\operatorname{vol}(L)$ be its covolume, for the Haar measure given by an orthonormal basis, and
$\Lambda(L)$ its last minimum. Then $\operatorname{vol}(L) \le \Lambda(L)^n$.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, §3, p. 2069 (the bound $\operatorname{vol}(\Omega) \le \Lambda(\Omega)^n$, from
Hadamard's inequality). -/
theorem covolume_le_lastMinimum_pow (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    covolume L ≤ lastMinimum L ^ finrank ℝ E := by
  unfold lastMinimum
  set n := finrank ℝ E
  set S : Set ℝ := {r : ℝ | 0 < r ∧ ∃ ω : Fin n → E,
    LinearIndependent ℝ ω ∧ ∀ i, ω i ∈ L ∧ ‖ω i‖ ≤ r}
  have hcov0 : 0 < covolume L := covolume_pos L volume
  -- Every `r ∈ S` has `vol(L) ≤ r ^ n`.
  have hS : ∀ r ∈ S, covolume L ≤ r ^ n := by
    rintro r ⟨hr, ω, hω, hωL⟩
    refine (covolume_le_prod_norm L ω hω fun i ↦ (hωL i).1).trans ?_
    calc ∏ i, ‖ω i‖ ≤ ∏ _i : Fin n, r := by
          gcongr with i
          exact (hωL i).2
      _ = r ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- `S` is nonempty: a basis of `L` lies in it.
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ L) = n := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  set B := ((Free.chooseBasis ℤ L).reindex (Fintype.equivFinOfCardEq hcard)).ofZLatticeBasis ℝ L
  have hne : S.Nonempty := by
    refine ⟨1 + ∑ i, ‖B i‖,
      add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ ↦ norm_nonneg _), B,
      B.linearIndependent, fun i ↦ ⟨?_, ?_⟩⟩
    · rw [Module.Basis.ofZLatticeBasis_apply]
      exact Subtype.mem _
    · have := Finset.single_le_sum (f := fun i ↦ ‖B i‖) (fun i _ ↦ norm_nonneg _)
        (Finset.mem_univ i)
      linarith
  rcases Nat.eq_zero_or_pos n with hn | hn
  · obtain ⟨r, hr⟩ := hne
    have h := hS r hr
    rw [hn, pow_zero] at h ⊢
    exact h
  -- For `n ≥ 1`, `vol(L) ^ (1/n)` is a lower bound of `S`.
  have hn0 : n ≠ 0 := hn.ne'
  have hlow : covolume L ^ ((n : ℝ)⁻¹) ≤ sInf S := by
    refine le_csInf hne fun r hr ↦ ?_
    have h := Real.rpow_le_rpow hcov0.le (hS r hr) (inv_nonneg.mpr (Nat.cast_nonneg n))
    rwa [Real.pow_rpow_inv_natCast hr.1.le hn0] at h
  have h1 := pow_le_pow_left₀ (Real.rpow_nonneg hcov0.le _) hlow n
  rwa [Real.rpow_inv_natCast_pow hcov0.le hn0] at h1

/-- **Minkowski's bound for the first minimum of a lattice** (Gaudron and Rémond, Lemme 3.1,
first inequality). Let $E$ be a Euclidean space of dimension $n$ and $L \subset E$ a lattice: a
discrete $\mathbb{Z}$-submodule that spans $E$. Let $\lambda(L)$ be its first minimum and
$\operatorname{vol}(L)$ its covolume, for the Haar measure of $E$ given by an orthonormal basis.
Then
$$\lambda(L) \le \sqrt{n}\, \operatorname{vol}(L)^{1/n}.$$
For $n = 0$ both sides are $0$.

The proof applies Minkowski's convex body theorem to the cube $\{x : |x_i| \le r\}$ in orthonormal
coordinates, for every $r > \operatorname{vol}(L)^{1/n}$.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, §3, p. 2069, Lemme 3.1, first inequality. -/
theorem firstMinimum_le_sqrt_finrank_mul_covolume_rpow (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] :
    firstMinimum L ≤ √(finrank ℝ E : ℝ) * covolume L ^ (1 / (finrank ℝ E : ℝ)) := by
  set n := finrank ℝ E
  set c := covolume L
  have hc0 : 0 < c := covolume_pos L volume
  have hbdd : BddBelow ((fun x : E ↦ ‖x‖) '' {x | x ∈ L ∧ x ≠ 0}) :=
    ⟨0, by rintro _ ⟨x, _, rfl⟩; exact norm_nonneg x⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- In dimension `0` there is no nonzero vector.
    have hE : Subsingleton E := Module.finrank_zero_iff.mp hn
    have : {x : E | x ∈ L ∧ x ≠ 0} = ∅ := by
      ext x; simp [Subsingleton.elim x 0]
    simp [firstMinimum, this, hn]
  have hn0 : n ≠ 0 := hn.ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hnR
  refine le_of_forall_gt_imp_ge_of_dense fun t ht ↦ ?_
  set r := t / √(n : ℝ)
  have hcr : c ^ (1 / (n : ℝ)) < r := by
    rw [lt_div_iff₀ hsq, mul_comm]; exact ht
  have hr0 : 0 < r := lt_of_le_of_lt (Real.rpow_nonneg hc0.le _) hcr
  have hcrn : c < r ^ n := by
    have := pow_lt_pow_left₀ hcr (Real.rpow_nonneg hc0.le _) hn0
    rwa [one_div, Real.rpow_inv_natCast_pow hc0.le hn0] at this
  -- The cube `{x : |x_i| ≤ r}` in orthonormal coordinates.
  set ob := stdOrthonormalBasis ℝ E
  set φ : E → (Fin n → ℝ) := fun x ↦ (ob.repr x).ofLp
  have hφ : MeasurePreserving φ volume volume :=
    (PiLp.volume_preserving_ofLp (Fin n)).comp ob.measurePreserving_repr
  set s : Set E := φ ⁻¹' Set.Icc (fun _ ↦ -r) (fun _ ↦ r)
  have hs_vol : volume s = ENNReal.ofReal ((2 * r) ^ n) := by
    rw [hφ.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by linarith)]
    congr 2
    ring
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
  -- Minkowski's convex body theorem.
  set b := Free.chooseBasis ℤ L
  have hfund := ZLattice.isAddFundamentalDomain b volume
  have hF : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) = ENNReal.ofReal c := by
    have hc := ZLattice.covolume_eq_measure_fundamentalDomain L volume hfund
    rw [measureReal_def] at hc
    rw [show c = _ from hc, ENNReal.ofReal_toReal]
    exact (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hlt : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)) * 2 ^ finrank ℝ E <
      volume s := by
    rw [hF, hs_vol, show (2 : ENNReal) ^ finrank ℝ E = ENNReal.ofReal (2 ^ n) by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat], ← ENNReal.ofReal_mul hc0.le,
      ENNReal.ofReal_lt_ofReal_iff (by positivity), mul_pow, mul_comm]
    exact mul_lt_mul_of_pos_left hcrn (by positivity)
  have : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  obtain ⟨x, hx0, hxs⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure (L := L.toAddSubgroup)
      hfund hs_symm hs_conv hlt
  -- The vector found has norm at most `√n r = t`.
  have hxnorm : ‖(x : E)‖ ≤ t := by
    rw [← ob.repr.norm_map, EuclideanSpace.norm_eq]
    have hcoord : ∀ i, ‖(ob.repr x).ofLp i‖ ^ 2 ≤ r ^ 2 := by
      intro i
      have h1 := hxs.1 i
      have h2 := hxs.2 i
      rw [Real.norm_eq_abs, sq_abs]
      simp only [φ] at h1 h2
      nlinarith
    calc √(∑ i, ‖(ob.repr x).ofLp i‖ ^ 2) ≤ √(∑ _i : Fin n, r ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ ↦ hcoord i)
      _ = √(n : ℝ) * r := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul hnR.le, Real.sqrt_sq hr0.le]
      _ = t := by rw [mul_div_cancel₀ _ hsq.ne']
  refine (csInf_le hbdd ⟨x, ⟨x.2, ?_⟩, rfl⟩).trans hxnorm
  exact fun h ↦ hx0 (Subtype.ext h)

end ZLattice
