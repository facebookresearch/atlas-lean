/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDefectDynamics
import Mathlib.Analysis.InnerProductSpace.Rayleigh









open Finset Matrix

namespace StatMech.FrontierD

noncomputable section

theorem sixVertexNoAdjacentTransferInfinity_isHermitian (N n : Nat) :
    (sixVertexNoAdjacentTransferInfinity N n).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro x y
  simp only [star_id_of_comm]
  exact sixVertexNoAdjacentTransferInfinity_symmetric N n y x

noncomputable def sixVertexNoAdjacentInfinityTopIndex
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    Fin (Fintype.card (SixVertexNoAdjacentSector N n)) := by
  letI : Nonempty (SixVertexNoAdjacentSector N n) :=
    ⟨sixVertexNoAdjacentAlternatingEven N n hn hhalf⟩
  exact ⟨0, Fintype.card_pos⟩

noncomputable def sixVertexNoAdjacentInfinityTopEigenvalue
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N) : Real :=
  (sixVertexNoAdjacentTransferInfinity_isHermitian N n).eigenvalues₀
    (sixVertexNoAdjacentInfinityTopIndex N n hn hhalf)

theorem sixVertexNoAdjacentInfinityTopEigenvalue_ge
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N)
    (i : Fin (Fintype.card (SixVertexNoAdjacentSector N n))) :
    (sixVertexNoAdjacentTransferInfinity_isHermitian N n).eigenvalues₀ i ≤
      sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
  apply (sixVertexNoAdjacentTransferInfinity_isHermitian N n).eigenvalues₀_antitone
  change (sixVertexNoAdjacentInfinityTopIndex N n hn hhalf).val ≤ i.val
  exact Nat.zero_le _

theorem sixVertexNoAdjacentInfinityTop_hasEigenvalue
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexNoAdjacentTransferInfinity N n))
      (sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf) := by
  exact LinearMap.IsSymmetric.hasEigenvalue_eigenvalues
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (sixVertexNoAdjacentTransferInfinity_isHermitian N n))
    finrank_euclideanSpace
    (sixVertexNoAdjacentInfinityTopIndex N n hn hhalf)

private theorem infinity_matrix_inner_le_abs
    {N n : Nat} (v : EuclideanSpace Real (SixVertexNoAdjacentSector N n)) :
    @inner Real _ _
        (Matrix.toEuclideanLin (sixVertexNoAdjacentTransferInfinity N n) v) v ≤
      @inner Real _ _
        (Matrix.toEuclideanLin (sixVertexNoAdjacentTransferInfinity N n)
          (euclideanAbs v)) (euclideanAbs v) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.ofLp_toLpLin, star_trivial, dotProduct,
    euclideanAbs, WithLp.ofLp_toLp]
  change (∑ i, v i * ∑ j, sixVertexNoAdjacentTransferInfinity N n i j * v j) ≤
    ∑ i, |v i| * ∑ j,
      sixVertexNoAdjacentTransferInfinity N n i j * |v j|
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    v i * (sixVertexNoAdjacentTransferInfinity N n i j * v j) ≤
        |v i * (sixVertexNoAdjacentTransferInfinity N n i j * v j)| :=
      le_abs_self _
    _ = |v i| * (sixVertexNoAdjacentTransferInfinity N n i j * |v j|) := by
      rw [abs_mul, abs_mul,
        abs_of_nonneg (sixVertexNoAdjacentTransferInfinity_nonneg N n i j)]

theorem sixVertexNoAdjacentInfinityTop_exists_nonnegative_eigenvector
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    ∃ v : EuclideanSpace Real (SixVertexNoAdjacentSector N n),
      v ≠ 0 ∧ (∀ i, 0 ≤ v i) ∧
        sixVertexNoAdjacentTransferInfinity N n *ᵥ (fun i => v i) =
          sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf •
            (fun i => v i) := by
  classical
  let A := sixVertexNoAdjacentTransferInfinity N n
  let T := Matrix.toEuclideanLin A
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (sixVertexNoAdjacentTransferInfinity_isHermitian N n)
  let T' := hT.toSelfAdjoint
  let p := sixVertexNoAdjacentAlternatingEven N n hn hhalf
  let e : EuclideanSpace Real (SixVertexNoAdjacentSector N n) :=
    EuclideanSpace.single p 1
  have he : ‖e‖ = 1 := by simp [e]
  have hsphere :
      (Metric.sphere (0 : EuclideanSpace Real
        (SixVertexNoAdjacentSector N n)) 1).Nonempty := ⟨e, by simp [he]⟩
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere
    (0 : EuclideanSpace Real (SixVertexNoAdjacentSector N n)) 1).exists_isMaxOn
      hsphere T'.val.reApplyInnerSelf_continuous.continuousOn
  have hvnorm : ‖v‖ = 1 := by simpa using hv
  let w := euclideanAbs v
  have hwnorm : ‖w‖ = 1 := by rw [norm_euclideanAbs, hvnorm]
  have hw : w ∈ Metric.sphere
      (0 : EuclideanSpace Real (SixVertexNoAdjacentSector N n)) 1 := by
    simp [hwnorm]
  have hle : T'.val.reApplyInnerSelf v ≤ T'.val.reApplyInnerSelf w := by
    simpa [T', T, A, ContinuousLinearMap.reApplyInnerSelf_apply] using
      infinity_matrix_inner_le_abs v
  have heq : T'.val.reApplyInnerSelf w = T'.val.reApplyInnerSelf v :=
    le_antisymm (hmax hw) hle
  have hwmax : IsMaxOn T'.val.reApplyInnerSelf
      (Metric.sphere 0 1) w := by
    intro z hz
    rw [heq]
    exact hmax hz
  have hwne : w ≠ 0 := by
    intro hw0
    rw [hw0, norm_zero] at hwnorm
    norm_num at hwnorm
  let μ : Real := T'.val.rayleighQuotient w
  have heig : Module.End.HasEigenvector T μ w := by
    have hwmax' : IsMaxOn T'.val.reApplyInnerSelf
        (Metric.sphere 0 ‖w‖) w := by simpa only [hwnorm] using hwmax
    exact T'.prop.hasEigenvector_of_isLocalExtrOn hwne (Or.inr hwmax'.localize)
  have hmu : μ = T'.val.reApplyInnerSelf w := by
    simp [μ, ContinuousLinearMap.rayleighQuotient, hwnorm]
  obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq finrank_euclideanSpace
    (Module.End.hasEigenvalue_of_hasEigenvector heig)
  have hμtop : μ ≤ sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
    rw [← hi]
    exact sixVertexNoAdjacentInfinityTopEigenvalue_ge N n hn hhalf i
  let i0 := sixVertexNoAdjacentInfinityTopIndex N n hn hhalf
  let u := hT.eigenvectorBasis finrank_euclideanSpace i0
  have hunorm : ‖u‖ = 1 :=
    hT.eigenvectorBasis finrank_euclideanSpace |>.orthonormal.1 i0
  have hu : u ∈ Metric.sphere
      (0 : EuclideanSpace Real (SixVertexNoAdjacentSector N n)) 1 := by
    simp [hunorm]
  have htopμ : sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf ≤ μ := by
    have hmaxu := hwmax hu
    have hmaxu' : T'.val.reApplyInnerSelf u ≤
        T'.val.reApplyInnerSelf w := hmaxu
    rw [← hmu] at hmaxu'
    have huEig := hT.apply_eigenvectorBasis finrank_euclideanSpace i0
    have huq : T'.val.reApplyInnerSelf u =
        sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
      rw [ContinuousLinearMap.reApplyInnerSelf_apply]
      change @inner Real _ _ (T u) u = _
      rw [huEig, inner_smul_left, real_inner_self_eq_norm_sq, hunorm]
      simp only [one_pow, mul_one]
      change hT.eigenvalues finrank_euclideanSpace i0 =
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr
          (sixVertexNoAdjacentTransferInfinity_isHermitian N n)).eigenvalues
            finrank_euclideanSpace i0
      exact congrArg (fun h : T.IsSymmetric =>
        h.eigenvalues finrank_euclideanSpace i0) (Subsingleton.elim _ _)
    linarith
  have hμeq : μ = sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf :=
    le_antisymm hμtop htopμ
  refine ⟨w, hwne, fun i => abs_nonneg _, ?_⟩
  have heqT : T w = μ • w := Module.End.mem_eigenspace_iff.mp heig.1
  have heqFn := congrArg WithLp.ofLp heqT
  simpa [T, A, hμeq, Matrix.ofLp_toLpLin] using heqFn

private theorem infinity_matrix_pow_mulVec_of_eigenvector
    {N n : Nat} (v : SixVertexNoAdjacentSector N n → Real) (μ : Real)
    (h : sixVertexNoAdjacentTransferInfinity N n *ᵥ v = μ • v) (k : Nat) :
    (sixVertexNoAdjacentTransferInfinity N n ^ k) *ᵥ v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring

private theorem infinity_nonnegative_eigenvector_pos
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N)
    {μ : Real} {v : EuclideanSpace Real (SixVertexNoAdjacentSector N n)}
    (hvne : v ≠ 0) (hvnonneg : ∀ i, 0 ≤ v i)
    (hveig : sixVertexNoAdjacentTransferInfinity N n *ᵥ (fun i => v i) =
      μ • (fun i => v i)) :
    ∀ i, 0 < v i := by
  classical
  intro i
  apply lt_of_le_of_ne (hvnonneg i)
  intro hvi
  have hvi0 : v i = 0 := hvi.symm
  obtain ⟨j, hvj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! hall
    apply hvne
    apply WithLp.ofLp_injective 2
    funext j
    simpa using hall j
  have hvjpos : 0 < v j := lt_of_le_of_ne (hvnonneg j) (Ne.symm hvj)
  obtain ⟨k, hk0, hk⟩ :=
    (Matrix.isIrreducible_iff_exists_pow_pos
      (sixVertexNoAdjacentTransferInfinity_nonneg N n)).mp
      (sixVertexNoAdjacentTransferInfinity_isIrreducible hn hhalf) i j
  have hpoweig := infinity_matrix_pow_mulVec_of_eigenvector
    (fun i => v i) μ hveig k
  have hi := congrFun hpoweig i
  have hsum : 0 < ((sixVertexNoAdjacentTransferInfinity N n ^ k) *ᵥ
      (fun i => v i)) i := by
    rw [Matrix.mulVec]
    apply Finset.sum_pos'
    · intro z _
      exact mul_nonneg
        (Matrix.pow_apply_nonneg
          (sixVertexNoAdjacentTransferInfinity_nonneg N n) k i z)
        (hvnonneg z)
    · exact ⟨j, Finset.mem_univ j, mul_pos hk hvjpos⟩
  simp only [Pi.smul_apply, smul_eq_mul, hvi0, mul_zero] at hi
  linarith

theorem sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    ∃ v : EuclideanSpace Real (SixVertexNoAdjacentSector N n),
      (∀ i, 0 < v i) ∧
        sixVertexNoAdjacentTransferInfinity N n *ᵥ (fun i => v i) =
          sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf •
            (fun i => v i) := by
  obtain ⟨v, hvne, hvnonneg, hveig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_nonnegative_eigenvector hn hhalf
  exact ⟨v, infinity_nonnegative_eigenvector_pos hn hhalf hvne hvnonneg hveig,
    hveig⟩

theorem sixVertexNoAdjacentInfinityTopEigenvalue_pos
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    0 < sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
  classical
  obtain ⟨v, hvpos, hveig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf
  let even := sixVertexNoAdjacentAlternatingEven N n hn hhalf
  let odd := sixVertexNoAdjacentAlternatingOdd N n hn hhalf
  have heo : (sixVertexNoAdjacentInfinityGraph N n).Adj even odd :=
    sixVertexNoAdjacentInfinityGraph_adj_alternating hn hhalf
  have hentry : sixVertexNoAdjacentTransferInfinity N n even odd = 1 := by
    rw [← sixVertexNoAdjacentInfinityGraph_adjMatrix]
    simp [SimpleGraph.adjMatrix, heo]
  have heven := congrFun hveig even
  have hsum : v odd ≤
      (sixVertexNoAdjacentTransferInfinity N n *ᵥ (fun i => v i)) even := by
    rw [Matrix.mulVec, dotProduct]
    calc
      v odd = sixVertexNoAdjacentTransferInfinity N n even odd * v odd := by
        rw [hentry, one_mul]
      _ ≤ ∑ i, sixVertexNoAdjacentTransferInfinity N n even i * v i := by
        apply Finset.single_le_sum
          (s := (Finset.univ : Finset (SixVertexNoAdjacentSector N n)))
          (f := fun i => sixVertexNoAdjacentTransferInfinity N n even i * v i)
        · intro j _
          exact mul_nonneg (sixVertexNoAdjacentTransferInfinity_nonneg N n even j)
            (hvpos j).le
        · exact Finset.mem_univ odd
  simp only [Pi.smul_apply, smul_eq_mul] at heven
  rw [heven] at hsum
  nlinarith [hvpos even, hvpos odd]

theorem sixVertexNoAdjacentInfinityTop_eigenspace_finrank
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    Module.finrank Real (Module.End.eigenspace
      (Matrix.toEuclideanLin (sixVertexNoAdjacentTransferInfinity N n))
      (sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf)) = 1 := by
  classical
  letI : Nonempty (SixVertexNoAdjacentSector N n) :=
    ⟨sixVertexNoAdjacentAlternatingEven N n hn hhalf⟩
  let A := sixVertexNoAdjacentTransferInfinity N n
  let T := Matrix.toEuclideanLin A
  let μ := sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf
  obtain ⟨v, hvpos, hveig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf
  have hvne : v ≠ 0 := by
    intro hv0
    have := hvpos (sixVertexNoAdjacentAlternatingEven N n hn hhalf)
    simp [hv0] at this
  have hvT : T v = μ • v := by
    apply WithLp.ofLp_injective 2
    simpa [T, A, μ, Matrix.ofLp_toLpLin] using hveig
  have hvMem : v ∈ Module.End.eigenspace T μ :=
    Module.End.mem_eigenspace_iff.mpr hvT
  let vv : Module.End.eigenspace T μ := ⟨v, hvMem⟩
  have hvvne : vv ≠ 0 := by
    intro h
    apply hvne
    exact Subtype.ext_iff.mp h
  apply finrank_eq_one vv hvvne
  intro zz
  let z : EuclideanSpace Real (SixVertexNoAdjacentSector N n) := zz.1
  have hzT : T z = μ • z := Module.End.mem_eigenspace_iff.mp zz.2
  let ratio : SixVertexNoAdjacentSector N n → Real := fun i => z i / v i
  have himage : (Finset.univ.image ratio).Nonempty :=
    Finset.image_nonempty.mpr Finset.univ_nonempty
  let r : Real := (Finset.univ.image ratio).min' himage
  have hr (i : SixVertexNoAdjacentSector N n) : r ≤ ratio i :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  obtain ⟨i0, _, hi0⟩ := Finset.mem_image.mp
    (Finset.min'_mem (Finset.univ.image ratio) himage)
  let w : EuclideanSpace Real (SixVertexNoAdjacentSector N n) := z - r • v
  have hwnonneg : ∀ i, 0 ≤ w i := by
    intro i
    change 0 ≤ z i - r * v i
    exact sub_nonneg.mpr ((le_div_iff₀ (hvpos i)).mp (hr i))
  have hwi0 : w i0 = 0 := by
    change z i0 - r * v i0 = 0
    have hir : ratio i0 = r := hi0
    dsimp [ratio] at hir
    rw [← hir]
    field_simp [(hvpos i0).ne']
    ring
  have hwT : T w = μ • w := by
    simp only [w, map_sub, map_smul, hzT, hvT]
    module
  have hweig : A *ᵥ (fun i => w i) = μ • (fun i => w i) := by
    have hwT' := congrArg WithLp.ofLp hwT
    simpa [T, A, Matrix.ofLp_toLpLin] using hwT'
  have hwzero : w = 0 := by
    by_contra hwne
    have hpos := infinity_nonnegative_eigenvector_pos hn hhalf hwne hwnonneg hweig i0
    rw [hwi0] at hpos
    exact lt_irrefl 0 hpos
  refine ⟨r, ?_⟩
  apply Subtype.ext
  change r • v = z
  exact (sub_eq_zero.mp hwzero).symm



theorem sixVertexNoAdjacentInfinityTop_isSimplePerron
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    0 < sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf ∧
      (∃ v : EuclideanSpace Real (SixVertexNoAdjacentSector N n),
        (∀ i, 0 < v i) ∧
          sixVertexNoAdjacentTransferInfinity N n *ᵥ (fun i => v i) =
            sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf •
              (fun i => v i)) ∧
      Module.finrank Real (Module.End.eigenspace
        (Matrix.toEuclideanLin (sixVertexNoAdjacentTransferInfinity N n))
        (sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf)) = 1 := by
  exact ⟨sixVertexNoAdjacentInfinityTopEigenvalue_pos hn hhalf,
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf,
    sixVertexNoAdjacentInfinityTop_eigenspace_finrank hn hhalf⟩


def sixVertexFulmekPerronBound (n r : Nat) : Real :=
  2 ^ r * ∏ j : Fin r,
    (1 + Real.cos (Real.pi * (2 * (j : Real) + 1) / (n + 2 * r)))

theorem sixVertexFulmekPerronBound_pos
    {n r : Nat} (hn : 0 < n) :
    0 < sixVertexFulmekPerronBound n r := by
  unfold sixVertexFulmekPerronBound
  apply mul_pos (by positivity)
  apply Finset.prod_pos
  intro j _
  let x : Real := Real.pi * (2 * (j : Real) + 1) / (n + 2 * r)
  have hden : (0 : Real) < n + 2 * r := by positivity
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have hj : (j : Nat) < r := j.isLt
  have hxpi : x < Real.pi := by
    dsimp [x]
    rw [div_lt_iff₀ hden]
    have hnumNat : 2 * (j : Nat) + 1 < n + 2 * r := by omega
    have hnumReal : 2 * (j : Real) + 1 < (n : Real) + 2 * (r : Real) := by
      exact_mod_cast hnumNat
    exact mul_lt_mul_of_pos_left hnumReal Real.pi_pos
  have hhalf : x / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hcos : 0 < Real.cos (x / 2) := Real.cos_pos_of_mem_Ioo hhalf
  have hid := Real.cos_two_mul (x / 2)
  have htwo : 2 * (x / 2) = x := by ring
  rw [htwo] at hid
  nlinarith [sq_pos_of_pos hcos]



theorem sixVertexNoAdjacentInfinityTop_le_of_positive_supersolution
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N)
    {R : Real} (q : SixVertexNoAdjacentSector N n → Real)
    (hqpos : ∀ i, 0 < q i)
    (hq : ∀ i, (sixVertexNoAdjacentTransferInfinity N n *ᵥ q) i ≤
      R * q i) :
    sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf ≤ R := by
  obtain ⟨v, hvpos, hveig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf
  let S : Real := ∑ i, v i * q i
  have hS : 0 < S := by
    let p := sixVertexNoAdjacentAlternatingEven N n hn hhalf
    apply Finset.sum_pos'
    · intro i _
      exact (mul_pos (hvpos i) (hqpos i)).le
    · exact ⟨p, Finset.mem_univ p, mul_pos (hvpos p) (hqpos p)⟩
  have hweighted :
      ∑ i, v i * (sixVertexNoAdjacentTransferInfinity N n *ᵥ q) i ≤
        ∑ i, v i * (R * q i) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hq i) (hvpos i).le
  have hleft :
      (∑ i, v i * (sixVertexNoAdjacentTransferInfinity N n *ᵥ q) i) =
        sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf * S := by
    simp only [Matrix.mulVec, dotProduct]
    calc
      (∑ i, v i * ∑ j,
          sixVertexNoAdjacentTransferInfinity N n i j * q j) =
          ∑ j, q j * ∑ i,
            sixVertexNoAdjacentTransferInfinity N n j i * v i := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        rw [sixVertexNoAdjacentTransferInfinity_symmetric N n]
        ring
      _ = ∑ j, q j *
          (sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf * v j) := by
        apply Finset.sum_congr rfl
        intro j _
        have hj := congrFun hveig j
        simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
          using congrArg (fun z : Real => q j * z) hj
      _ = sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf * S := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hright : (∑ i, v i * (R * q i)) = R * S := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hleft, hright] at hweighted
  nlinarith




noncomputable def sixVertexNoAdjacentZeroExtend {N n : Nat}
    (q : SixVertexNoAdjacentSector N n → Real) : SixVertexSector N n → Real := by
  classical
  exact fun x => if hx : SixVertexSectorNoAdjacent x then q ⟨x, hx⟩ else 0

@[simp] theorem sixVertexNoAdjacentZeroExtend_apply
    {N n : Nat} (q : SixVertexNoAdjacentSector N n → Real)
    (x : SixVertexNoAdjacentSector N n) :
    sixVertexNoAdjacentZeroExtend q x.1 = q x := by
  simp [sixVertexNoAdjacentZeroExtend, x.2]

theorem sixVertexSectorTransferInfinity_mulVec_zeroExtend_apply
    {N n : Nat} (q : SixVertexNoAdjacentSector N n → Real)
    (x : SixVertexSector N n) (hx : SixVertexSectorNoAdjacent x) :
    (sixVertexSectorTransferInfinity N n *ᵥ
        sixVertexNoAdjacentZeroExtend q) x =
      (sixVertexNoAdjacentTransferInfinity N n *ᵥ q) ⟨x, hx⟩ := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  change (∑ y : SixVertexSector N n,
    sixVertexSectorTransferInfinity N n x y *
      sixVertexNoAdjacentZeroExtend q y) =
    ∑ y : SixVertexNoAdjacentSector N n,
      sixVertexSectorTransferInfinity N n x y.1 * q y
  calc
    (∑ y : SixVertexSector N n,
      sixVertexSectorTransferInfinity N n x y *
        sixVertexNoAdjacentZeroExtend q y) =
        ∑ y ∈ (Finset.univ.filter fun y : SixVertexSector N n ↦
          SixVertexSectorNoAdjacent y),
          sixVertexSectorTransferInfinity N n x y *
            sixVertexNoAdjacentZeroExtend q y := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : SixVertexSectorNoAdjacent y <;>
        simp [sixVertexNoAdjacentZeroExtend, hy]
    _ = ∑ y : SixVertexNoAdjacentSector N n,
        sixVertexSectorTransferInfinity N n x y.1 *
          sixVertexNoAdjacentZeroExtend q y.1 :=
      Finset.sum_subtype _ (by simp) _
    _ = ∑ y : SixVertexNoAdjacentSector N n,
        sixVertexSectorTransferInfinity N n x y.1 * q y := by
      apply Finset.sum_congr rfl
      intro y _
      simp

theorem sixVertexSectorTransferInfinity_mulVec_zeroExtend
    {N n : Nat} (q : SixVertexNoAdjacentSector N n → Real) :
    sixVertexSectorTransferInfinity N n *ᵥ sixVertexNoAdjacentZeroExtend q =
      sixVertexNoAdjacentZeroExtend
        (sixVertexNoAdjacentTransferInfinity N n *ᵥ q) := by
  funext x
  by_cases hx : SixVertexSectorNoAdjacent x
  · rw [sixVertexSectorTransferInfinity_mulVec_zeroExtend_apply q x hx]
    simp [sixVertexNoAdjacentZeroExtend, hx]
  · simp only [Matrix.mulVec, dotProduct]
    rw [show (∑ y, sixVertexSectorTransferInfinity N n x y *
        sixVertexNoAdjacentZeroExtend q y) = 0 by
      apply Finset.sum_eq_zero
      intro y _
      rw [sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_left hx]
      simp]
    simp [sixVertexNoAdjacentZeroExtend, hx]



theorem sixVertexSectorTransferInfinity_exists_Perron_eigenvector
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    ∃ v : EuclideanSpace Real (SixVertexSector N n),
      v ≠ 0 ∧
      (sixVertexSectorTransferInfinity N n *ᵥ (fun i ↦ v i) =
        sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf •
          (fun i ↦ v i)) := by
  obtain ⟨w, hwpos, hweig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf
  let v : EuclideanSpace Real (SixVertexSector N n) :=
    WithLp.toLp 2 (sixVertexNoAdjacentZeroExtend (fun i ↦ w i))
  have hvne : v ≠ 0 := by
    intro hv
    let p := sixVertexNoAdjacentAlternatingEven N n hn hhalf
    have hp := congrArg (fun z : EuclideanSpace Real (SixVertexSector N n) ↦
      z p.1) hv
    simp [v, p] at hp
    exact (hwpos p).ne' hp
  refine ⟨v, hvne, ?_⟩
  rw [show (fun i ↦ v i) =
      sixVertexNoAdjacentZeroExtend (fun i ↦ w i) by rfl,
    sixVertexSectorTransferInfinity_mulVec_zeroExtend, hweig]
  funext x
  by_cases hx : SixVertexSectorNoAdjacent x
  · simp [sixVertexNoAdjacentZeroExtend, hx]
  · simp [sixVertexNoAdjacentZeroExtend, hx]



theorem sixVertexSectorTransferInfinity_Perron_eigenspace_finrank
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    Module.finrank Real (Module.End.eigenspace
      (Matrix.toEuclideanLin (sixVertexSectorTransferInfinity N n))
      (sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf)) = 1 := by
  classical
  let A := sixVertexSectorTransferInfinity N n
  let B := sixVertexNoAdjacentTransferInfinity N n
  let T := Matrix.toEuclideanLin A
  let U := Matrix.toEuclideanLin B
  let μ := sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf
  have hμpos : 0 < μ := sixVertexNoAdjacentInfinityTopEigenvalue_pos hn hhalf
  obtain ⟨v, hvpos, hveig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf
  let V : EuclideanSpace Real (SixVertexSector N n) :=
    WithLp.toLp 2 (sixVertexNoAdjacentZeroExtend (fun i ↦ v i))
  have hVT : T V = μ • V := by
    apply WithLp.ofLp_injective 2
    simp only [T, A, V, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
      WithLp.ofLp_smul]
    rw [sixVertexSectorTransferInfinity_mulVec_zeroExtend, hveig]
    funext x
    by_cases hx : SixVertexSectorNoAdjacent x <;>
      simp [μ, sixVertexNoAdjacentZeroExtend, hx]
  have hVMem : V ∈ Module.End.eigenspace T μ :=
    Module.End.mem_eigenspace_iff.mpr hVT
  let VV : Module.End.eigenspace T μ := ⟨V, hVMem⟩
  have hVVne : VV ≠ 0 := by
    intro hzero
    let p := sixVertexNoAdjacentAlternatingEven N n hn hhalf
    have hp := congrArg (fun z : EuclideanSpace Real (SixVertexSector N n) ↦
      z p.1) (Subtype.ext_iff.mp hzero)
    simp [VV, V, p] at hp
    exact (hvpos p).ne' hp
  apply finrank_eq_one VV hVVne
  intro zz
  let z : EuclideanSpace Real (SixVertexSector N n) := zz.1
  have hzT : T z = μ • z := Module.End.mem_eigenspace_iff.mp zz.2
  have hzeig : A *ᵥ (fun i ↦ z i) = μ • (fun i ↦ z i) := by
    have hz := congrArg WithLp.ofLp hzT
    simpa [T, A, Matrix.ofLp_toLpLin] using hz
  have hzinactive (x : SixVertexSector N n)
      (hx : ¬ SixVertexSectorNoAdjacent x) : z x = 0 := by
    have hxcoord := congrFun hzeig x
    have hxleft : (A *ᵥ (fun i ↦ z i)) x = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro y _
      simp [A, sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_left hx]
    rw [hxleft] at hxcoord
    simp only [Pi.smul_apply, smul_eq_mul] at hxcoord
    nlinarith
  let w : EuclideanSpace Real (SixVertexNoAdjacentSector N n) :=
    WithLp.toLp 2 (fun i ↦ z i.1)
  have hzext : sixVertexNoAdjacentZeroExtend (fun i ↦ w i) =
      (fun x ↦ z x) := by
    funext x
    by_cases hx : SixVertexSectorNoAdjacent x
    · simp [sixVertexNoAdjacentZeroExtend, hx, w]
    · simp [sixVertexNoAdjacentZeroExtend, hx, hzinactive x hx]
  have hweig : B *ᵥ (fun i ↦ w i) = μ • (fun i ↦ w i) := by
    funext x
    have hxcoord := congrFun hzeig x.1
    rw [← hzext,
      sixVertexSectorTransferInfinity_mulVec_zeroExtend_apply
        (fun i ↦ w i) x.1 x.2] at hxcoord
    simpa [A, B, μ, sixVertexNoAdjacentZeroExtend, x.2] using hxcoord
  have hwT : U w = μ • w := by
    apply WithLp.ofLp_injective 2
    simpa [U, B, Matrix.ofLp_toLpLin] using hweig
  have hwMem : w ∈ Module.End.eigenspace U μ :=
    Module.End.mem_eigenspace_iff.mpr hwT
  have hvT : U v = μ • v := by
    apply WithLp.ofLp_injective 2
    simpa [U, B, μ, Matrix.ofLp_toLpLin] using hveig
  have hvMem : v ∈ Module.End.eigenspace U μ :=
    Module.End.mem_eigenspace_iff.mpr hvT
  let vv : Module.End.eigenspace U μ := ⟨v, hvMem⟩
  have hvvne : vv ≠ 0 := by
    intro hzero
    let p := sixVertexNoAdjacentAlternatingEven N n hn hhalf
    have hp := congrArg (fun q : EuclideanSpace Real
      (SixVertexNoAdjacentSector N n) ↦ q p) (Subtype.ext_iff.mp hzero)
    simp [vv] at hp
    exact (hvpos p).ne' hp
  have hactiveRank : Module.finrank Real (Module.End.eigenspace U μ) = 1 := by
    simpa [U, B, μ] using
      sixVertexNoAdjacentInfinityTop_eigenspace_finrank hn hhalf
  have hspan : Real ∙ vv = ⊤ :=
    (finrank_eq_one_iff_of_nonzero vv hvvne).mp hactiveRank
  have hwmemspan : (⟨w, hwMem⟩ : Module.End.eigenspace U μ) ∈
      Real ∙ vv := by
    rw [hspan]
    trivial
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hwmemspan
  refine ⟨r, Subtype.ext ?_⟩
  change r • V = z
  apply WithLp.ofLp_injective 2
  funext x
  by_cases hx : SixVertexSectorNoAdjacent x
  · have hr' := congrArg (fun q : EuclideanSpace Real
        (SixVertexNoAdjacentSector N n) ↦ q ⟨x, hx⟩)
      (congrArg Subtype.val hr)
    simpa [VV, V, vv, w, sixVertexNoAdjacentZeroExtend, hx] using hr'
  · simp [V, sixVertexNoAdjacentZeroExtend, hx, hzinactive x hx]

theorem sixVertexSectorTransferInfinity_isHermitian (N n : Nat) :
    (sixVertexSectorTransferInfinity N n).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro x y
  simp only [star_id_of_comm]
  exact sixVertexSectorTransferInfinity_symmetric N n y x

noncomputable def sixVertexSectorInfinityTopIndex
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    Fin (Fintype.card (SixVertexSector N n)) := by
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty (by omega)
  exact ⟨0, Fintype.card_pos⟩


noncomputable def sixVertexSectorInfinityTopEigenvalue
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N) : Real :=
  (sixVertexSectorTransferInfinity_isHermitian N n).eigenvalues₀
    (sixVertexSectorInfinityTopIndex N n hn hhalf)

theorem sixVertexSectorInfinityTopEigenvalue_ge
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N)
    (i : Fin (Fintype.card (SixVertexSector N n))) :
    (sixVertexSectorTransferInfinity_isHermitian N n).eigenvalues₀ i ≤
      sixVertexSectorInfinityTopEigenvalue N n hn hhalf := by
  apply (sixVertexSectorTransferInfinity_isHermitian N n).eigenvalues₀_antitone
  change (sixVertexSectorInfinityTopIndex N n hn hhalf).val ≤ i.val
  exact Nat.zero_le _

theorem sixVertexSectorInfinityTop_hasEigenvalue
    (N n : Nat) (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexSectorTransferInfinity N n))
      (sixVertexSectorInfinityTopEigenvalue N n hn hhalf) := by
  exact LinearMap.IsSymmetric.hasEigenvalue_eigenvalues
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (sixVertexSectorTransferInfinity_isHermitian N n))
    finrank_euclideanSpace
    (sixVertexSectorInfinityTopIndex N n hn hhalf)



theorem sixVertexSectorInfinityTop_le_of_positive_supersolution
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N)
    {R : Real} (q : SixVertexSector N n → Real)
    (hqpos : ∀ i, 0 < q i)
    (hq : ∀ i, (sixVertexSectorTransferInfinity N n *ᵥ q) i ≤
      R * q i) :
    sixVertexSectorInfinityTopEigenvalue N n hn hhalf ≤ R := by
  classical
  let A := sixVertexSectorTransferInfinity N n
  let T := Matrix.toEuclideanLin A
  let μ := sixVertexSectorInfinityTopEigenvalue N n hn hhalf
  obtain ⟨z, hzmem, hzne⟩ :=
    (sixVertexSectorInfinityTop_hasEigenvalue N n hn hhalf).exists_hasEigenvector
  have hzT : T z = μ • z := Module.End.mem_eigenspace_iff.mp hzmem
  have hzeig : A *ᵥ (fun i ↦ z i) = μ • (fun i ↦ z i) := by
    have hz := congrArg WithLp.ofLp hzT
    simpa [T, A, Matrix.ofLp_toLpLin] using hz
  let S : Real := ∑ i, q i * |z i|
  have hS : 0 < S := by
    obtain ⟨j, hzj⟩ : ∃ j, z j ≠ 0 := by
      by_contra! hall
      apply hzne
      apply WithLp.ofLp_injective 2
      funext j
      simpa using hall j
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (hqpos i).le (abs_nonneg _)
    · exact ⟨j, Finset.mem_univ j,
        mul_pos (hqpos j) (abs_pos.mpr hzj)⟩
  have hcoord (i : SixVertexSector N n) :
      |μ| * |z i| ≤ ∑ j, A i j * |z j| := by
    have hi := congrFun hzeig i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
    rw [← abs_mul, ← hi]
    calc
      |∑ j, A i j * z j| ≤ ∑ j, |A i j * z j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, A i j * |z j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_of_nonneg]
        exact sixVertexSectorTransferInfinity_nonneg N n i j
  have hweighted :
      ∑ i, q i * (|μ| * |z i|) ≤
        ∑ i, q i * ∑ j, A i j * |z j| := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hcoord i) (hqpos i).le
  have hleft : ∑ i, q i * (|μ| * |z i|) = |μ| * S := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htranspose :
      (∑ i, q i * ∑ j, A i j * |z j|) =
        ∑ j, |z j| * (A *ᵥ q) j := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [show A i j = A j i by
      exact sixVertexSectorTransferInfinity_symmetric N n i j]
    ring
  have hright : (∑ j, |z j| * (A *ᵥ q) j) ≤ R * S := by
    calc
      (∑ j, |z j| * (A *ᵥ q) j) ≤
          ∑ j, |z j| * (R * q j) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hq j) (abs_nonneg _)
      _ = R * S := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [hleft, htranspose] at hweighted
  have habs : |μ| * S ≤ R * S := hweighted.trans hright
  have hmule : μ ≤ |μ| := le_abs_self μ
  nlinarith



theorem sixVertexSectorInfinityTopEigenvalue_eq_noAdjacent
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    sixVertexSectorInfinityTopEigenvalue N n hn hhalf =
      sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf := by
  classical
  let ρ := sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf
  have hρpos : 0 < ρ := sixVertexNoAdjacentInfinityTopEigenvalue_pos hn hhalf
  obtain ⟨v, hvpos, hveig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf
  let q : SixVertexSector N n → Real := fun x ↦
    if hx : SixVertexSectorNoAdjacent x then v ⟨x, hx⟩ else 1
  have hqpos : ∀ x, 0 < q x := by
    intro x
    by_cases hx : SixVertexSectorNoAdjacent x
    · simp [q, hx, hvpos ⟨x, hx⟩]
    · simp [q, hx]
  have hmul : sixVertexSectorTransferInfinity N n *ᵥ q =
      sixVertexSectorTransferInfinity N n *ᵥ
        sixVertexNoAdjacentZeroExtend (fun i ↦ v i) := by
    funext x
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : SixVertexSectorNoAdjacent y
    · simp [q, hy, sixVertexNoAdjacentZeroExtend]
    · rw [sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_right x hy]
      simp
  have hq : ∀ x, (sixVertexSectorTransferInfinity N n *ᵥ q) x ≤ ρ * q x := by
    intro x
    rw [hmul, sixVertexSectorTransferInfinity_mulVec_zeroExtend, hveig]
    by_cases hx : SixVertexSectorNoAdjacent x
    · simp [q, hx, sixVertexNoAdjacentZeroExtend, ρ]
    · simp [q, hx, sixVertexNoAdjacentZeroExtend, hρpos.le]
  have hfullLe : sixVertexSectorInfinityTopEigenvalue N n hn hhalf ≤ ρ :=
    sixVertexSectorInfinityTop_le_of_positive_supersolution hn hhalf q hqpos hq
  have hactiveEig : Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexSectorTransferInfinity N n)) ρ := by
    obtain ⟨w, hwne, hweigFull⟩ :=
      sixVertexSectorTransferInfinity_exists_Perron_eigenvector hn hhalf
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, hwne⟩
    apply Module.End.mem_eigenspace_iff.mpr
    apply WithLp.ofLp_injective 2
    simpa [ρ, Matrix.ofLp_toLpLin] using hweigFull
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (sixVertexSectorTransferInfinity_isHermitian N n)
  obtain ⟨i, hi⟩ := hsym.exists_eigenvalues_eq finrank_euclideanSpace hactiveEig
  have hactiveLe : ρ ≤ sixVertexSectorInfinityTopEigenvalue N n hn hhalf := by
    rw [← hi]
    exact sixVertexSectorInfinityTopEigenvalue_ge N n hn hhalf i
  exact le_antisymm hfullLe hactiveLe


theorem sixVertexSectorInfinityTop_isSimplePerron
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    0 < sixVertexSectorInfinityTopEigenvalue N n hn hhalf ∧
      Module.finrank Real (Module.End.eigenspace
        (Matrix.toEuclideanLin (sixVertexSectorTransferInfinity N n))
        (sixVertexSectorInfinityTopEigenvalue N n hn hhalf)) = 1 := by
  rw [sixVertexSectorInfinityTopEigenvalue_eq_noAdjacent hn hhalf]
  exact ⟨sixVertexNoAdjacentInfinityTopEigenvalue_pos hn hhalf,
    sixVertexSectorTransferInfinity_Perron_eigenspace_finrank hn hhalf⟩

end

end StatMech.FrontierD
