/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexPerronLimit









open Finset Filter Matrix Topology

namespace StatMech.FrontierD

noncomputable section



theorem hermitian_trace_sq_eq_sum_eigenvalues₀_sq
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α Real) (hA : A.IsHermitian) :
    Matrix.trace (A ^ 2) =
      ∑ i : Fin (Fintype.card α), hA.eigenvalues₀ i ^ 2 := by
  have htrace : Matrix.trace (A ^ 2) =
      ∑ i : α, hA.eigenvalues i ^ 2 := by
    conv_lhs =>
      rw [hA.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply,
        Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
        Matrix.diagonal_pow, Matrix.trace_diagonal]
    simp
  rw [htrace]
  symm
  apply Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin _))
  intro i
  simp [Matrix.IsHermitian.eigenvalues]



theorem hermitian_three_eigenvalues_sq_le_trace_sq
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (A : Matrix α α Real) (hA : A.IsHermitian)
    {a b d : Real}
    (ha : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) a)
    (hb : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) b)
    (hd : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) d)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    a ^ 2 + b ^ 2 + d ^ 2 ≤ Matrix.trace (A ^ 2) := by
  classical
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  obtain ⟨ia, hia⟩ :=
    hT.exists_eigenvalues_eq finrank_euclideanSpace ha
  obtain ⟨ib, hib⟩ :=
    hT.exists_eigenvalues_eq finrank_euclideanSpace hb
  obtain ⟨id, hid⟩ :=
    hT.exists_eigenvalues_eq finrank_euclideanSpace hd
  have hia' : hA.eigenvalues₀ ia = a := by
    simpa [hT, Matrix.IsHermitian.eigenvalues] using hia
  have hib' : hA.eigenvalues₀ ib = b := by
    simpa [hT, Matrix.IsHermitian.eigenvalues] using hib
  have hid' : hA.eigenvalues₀ id = d := by
    simpa [hT, Matrix.IsHermitian.eigenvalues] using hid
  have hiab : ia ≠ ib := by
    intro h
    apply hab
    rw [← hia', ← hib', h]
  have hiad : ia ≠ id := by
    intro h
    apply had
    rw [← hia', ← hid', h]
  have hibd : ib ≠ id := by
    intro h
    apply hbd
    rw [← hib', ← hid', h]
  let s : Finset (Fin (Fintype.card α)) := {ia, ib, id}
  have hsubset : s ⊆ Finset.univ := Finset.subset_univ s
  have hsum :
      (∑ i ∈ s, hA.eigenvalues₀ i ^ 2) =
        a ^ 2 + b ^ 2 + d ^ 2 := by
    simp [s, hiab, hiad, hibd, hia', hib', hid', add_assoc]
  rw [← hsum, hermitian_trace_sq_eq_sum_eigenvalues₀_sq A hA]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun i hi _ => sq_nonneg (hA.eigenvalues₀ i))




theorem exists_eigenvalue_le_rayleigh
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (A : Matrix α α Real) (hA : A.IsHermitian)
    (v : EuclideanSpace Real α) (hv : v ≠ 0) :
    ∃ μ : Real,
      Module.End.HasEigenvalue (Matrix.toEuclideanLin A) μ ∧
      μ ≤ @RCLike.re Real _
          (inner Real (Matrix.toEuclideanLin A v) v) / ‖v‖ ^ 2 := by
  let T := Matrix.toEuclideanLin A
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let q : {x : EuclideanSpace Real α // x ≠ 0} → Real := fun x =>
    @RCLike.re Real _ (inner Real (T x) x) / ‖(x : EuclideanSpace Real α)‖ ^ 2
  let μ : Real := ⨅ x, q x
  have hμ : Module.End.HasEigenvalue T μ := by
    exact hT.hasEigenvalue_iInf_of_finiteDimensional
  have hq_bdd : BddBelow (Set.range q) := by
    let Tc : EuclideanSpace Real α →L[Real] EuclideanSpace Real α :=
      LinearMap.toContinuousLinearMap T
    refine ⟨-‖Tc‖, ?_⟩
    rintro y ⟨x, rfl⟩
    have habs : |Tc.rayleighQuotient x| ≤ ‖Tc‖ :=
      Tc.rayleighQuotient_le_norm x
    have hneg : -‖Tc‖ ≤ Tc.rayleighQuotient x := by
      linarith [neg_abs_le (Tc.rayleighQuotient x)]
    exact hneg
  have hle : μ ≤ q ⟨v, hv⟩ := ciInf_le hq_bdd ⟨v, hv⟩
  exact ⟨μ, hμ, hle⟩



theorem sixVertexSectorTransferNormalized_isHermitian
    (N n : Nat) (c : Real) :
    (sixVertexSectorTransferNormalized N n c).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro x y
  simp only [starRingEnd_apply, star_trivial]
  unfold sixVertexSectorTransferNormalized sixVertexSectorTransfer
  rw [sixVertexTransfer_symmetric N c
    (sixVertexSectorRow y) (sixVertexSectorRow x)]



theorem sixVertexSectorTransferNormalized_hasEigenvalue
    {N n : Nat} {c μ : Real} (hscale : (c ^ 2 - 2) ^ n ≠ 0)
    (hμ : Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)) μ) :
    Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexSectorTransferNormalized N n c))
      (μ / (c ^ 2 - 2) ^ n) := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv.2⟩
  have heig := hv.apply_eq_smul
  apply WithLp.ofLp_injective 2
  funext x
  have hx := congrArg
    (fun z : EuclideanSpace Real (SixVertexSector N n) => z x) heig
  simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Pi.smul_apply,
    smul_eq_mul] at hx ⊢
  simp only [Matrix.mulVec, dotProduct] at hx ⊢
  have hsum :
      (∑ i, sixVertexSectorTransferNormalized N n c x i * v i) =
        (∑ i, sixVertexSectorTransfer N n c x i * v i) /
          (c ^ 2 - 2) ^ n := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    unfold sixVertexSectorTransferNormalized
    ring
  rw [hsum, hx]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  field_simp [hscale]



theorem sixVertexSectorTransferNormalized_top_hasEigenvalue
    {N n : Nat} (hn : n ≤ N) {c : Real}
    (hscale : (c ^ 2 - 2) ^ n ≠ 0) :
    Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexSectorTransferNormalized N n c))
      (sixVertexSectorTopEigenvalue N n hn c / (c ^ 2 - 2) ^ n) :=
  sixVertexSectorTransferNormalized_hasEigenvalue hscale
    (sixVertexSectorTop_hasEigenvalue N n hn c)




theorem tendsto_trace_sixVertexSectorTransferNormalized_sq_half
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n = N) :
    Tendsto (fun c => Matrix.trace
      (sixVertexSectorTransferNormalized N n c ^ 2)) atTop (nhds 2) := by
  classical
  have hentry (x y : SixVertexSector N n) :
      Tendsto (fun c =>
          sixVertexSectorTransferNormalized N n c x y *
            sixVertexSectorTransferNormalized N n c y x)
        atTop (nhds (sixVertexSectorTransferInfinity N n x y *
          sixVertexSectorTransferInfinity N n y x)) := by
    exact (tendsto_sixVertexSectorTransfer_normalized_atTop hn x y).mul
      (tendsto_sixVertexSectorTransfer_normalized_atTop hn y x)
  have hsum : Tendsto (fun c =>
      ∑ x : SixVertexSector N n, ∑ y : SixVertexSector N n,
        sixVertexSectorTransferNormalized N n c x y *
          sixVertexSectorTransferNormalized N n c y x) atTop
      (nhds (∑ x : SixVertexSector N n, ∑ y : SixVertexSector N n,
        sixVertexSectorTransferInfinity N n x y *
          sixVertexSectorTransferInfinity N n y x)) := by
    exact tendsto_finsetSum Finset.univ fun x _ =>
      tendsto_finsetSum Finset.univ fun y _ => hentry x y
  have hlimit :
      (∑ x : SixVertexSector N n, ∑ y : SixVertexSector N n,
        sixVertexSectorTransferInfinity N n x y *
          sixVertexSectorTransferInfinity N n y x) = 2 := by
    let even := sixVertexAlternatingEvenSector N n hhalf.le
    let odd := sixVertexAlternatingOddSector N n hhalf.le
    have hne : even ≠ odd :=
      (sixVertexInfinityGraph_adj_alternating_of_half hn hhalf).ne
    let f : SixVertexSector N n → Real := fun x =>
      ∑ y : SixVertexSector N n,
        sixVertexSectorTransferInfinity N n x y *
          sixVertexSectorTransferInfinity N n y x
    rw [show (∑ x : SixVertexSector N n, ∑ y : SixVertexSector N n,
        sixVertexSectorTransferInfinity N n x y *
          sixVertexSectorTransferInfinity N n y x) = ∑ x, f x by rfl]
    rw [← Finset.add_sum_erase Finset.univ f (a := even)
      (Finset.mem_univ even)]
    rw [← Finset.add_sum_erase (Finset.univ.erase even) f (a := odd)
      (by simp [Ne.symm hne])]
    have heven :
        (∑ y : SixVertexSector N n,
          sixVertexSectorTransferInfinity N n even y *
            sixVertexSectorTransferInfinity N n y even) = 1 := by
      rw [Fintype.sum_eq_single odd]
      · simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
          even, odd, hne, Ne.symm hne]
      · intro y hy
        simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
          even, odd, hne, Ne.symm hne, hy]
    have hodd :
        (∑ y : SixVertexSector N n,
          sixVertexSectorTransferInfinity N n odd y *
            sixVertexSectorTransferInfinity N n y odd) = 1 := by
      rw [Fintype.sum_eq_single even]
      · simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
          even, odd, hne, Ne.symm hne]
      · intro y hy
        simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
          even, odd, hne, Ne.symm hne, hy]
    have hother (x : SixVertexSector N n)
        (hxe : x ≠ even) (hxo : x ≠ odd) :
        (∑ y : SixVertexSector N n,
          sixVertexSectorTransferInfinity N n x y *
            sixVertexSectorTransferInfinity N n y x) = 0 := by
      simp [sixVertexSectorTransferInfinity_apply_half hn hhalf,
        even, odd, hxe, hxo]
    change f even + (f odd + ∑ x ∈ (Finset.univ.erase even).erase odd,
      f x) = 2
    rw [show f even = 1 from heven, show f odd = 1 from hodd]
    rw [Finset.sum_eq_zero (fun x hx => by
      have hx' := Finset.mem_erase.mp hx
      exact hother x (Finset.mem_erase.mp hx'.2).1 hx'.1)]
    norm_num
  rw [hlimit] at hsum
  convert hsum using 1
  funext c
  simp [Matrix.trace, Matrix.mul_apply, pow_two]



theorem sixVertexSectorTransfer_alternatingDifference_rayleigh
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n = N) (c : Real) :
    let even := sixVertexAlternatingEvenSector N n hhalf.le
    let odd := sixVertexAlternatingOddSector N n hhalf.le
    let v : SixVertexSector N n → Real := fun x =>
      if x = even then 1 else if x = odd then -1 else 0
    (∑ x, v x * (sixVertexSectorTransfer N n c *ᵥ v) x) /
        (∑ x, v x ^ 2) = 2 - c ^ (2 * n) := by
  classical
  let even := sixVertexAlternatingEvenSector N n hhalf.le
  let odd := sixVertexAlternatingOddSector N n hhalf.le
  let v : SixVertexSector N n → Real := fun x =>
    if x = even then 1 else if x = odd then -1 else 0
  have hne : even ≠ odd :=
    (sixVertexInfinityGraph_adj_alternating_of_half hn hhalf).ne
  have hden : (∑ x, v x ^ 2) = 2 := by
    rw [← Finset.add_sum_erase Finset.univ (fun x => v x ^ 2) (a := even)
      (Finset.mem_univ even)]
    rw [← Finset.add_sum_erase (Finset.univ.erase even)
      (fun x => v x ^ 2) (a := odd) (by simp [Ne.symm hne])]
    rw [Finset.sum_eq_zero (fun x hx => by
      have hx' := Finset.mem_erase.mp hx
      simp [v, (Finset.mem_erase.mp hx'.2).1, hx'.1])]
    norm_num [v, hne, Ne.symm hne]
  have hcross : sixVertexSectorTransfer N n c even odd = c ^ (2 * n) := by
    have hadj := sixVertexInfinityGraph_adj_alternating_of_half hn hhalf
    have hrowne : sixVertexSectorRow even ≠ sixVertexSectorRow odd :=
      fun h => hne (sixVertexSectorRow_injective h)
    change sixVertexTransfer N c (sixVertexSectorRow even)
      (sixVertexSectorRow odd) = c ^ (2 * n)
    rw [sixVertexTransfer, if_neg hrowne, if_pos hadj.2.1, hadj.2.2]
  have hdiagEven : sixVertexSectorTransfer N n c even even = 2 := by
    simp [sixVertexSectorTransfer, sixVertexTransfer]
  have hdiagOdd : sixVertexSectorTransfer N n c odd odd = 2 := by
    simp [sixVertexSectorTransfer, sixVertexTransfer]
  have hnum :
      (∑ x, v x * (sixVertexSectorTransfer N n c *ᵥ v) x) =
        2 * (2 - c ^ (2 * n)) := by
    let f : SixVertexSector N n → Real := fun x =>
      v x * (sixVertexSectorTransfer N n c *ᵥ v) x
    rw [show (∑ x, v x * (sixVertexSectorTransfer N n c *ᵥ v) x) =
      ∑ x, f x by rfl]
    rw [← Finset.add_sum_erase Finset.univ f (a := even)
      (Finset.mem_univ even)]
    rw [← Finset.add_sum_erase (Finset.univ.erase even) f (a := odd)
      (by simp [Ne.symm hne])]
    have heven : (sixVertexSectorTransfer N n c *ᵥ v) even =
        2 - c ^ (2 * n) := by
      rw [Matrix.mulVec, dotProduct]
      let g : SixVertexSector N n → Real := fun x =>
        sixVertexSectorTransfer N n c even x * v x
      change ∑ x, g x = 2 - c ^ (2 * n)
      rw [← Finset.add_sum_erase Finset.univ g (a := even)
        (Finset.mem_univ even)]
      rw [← Finset.add_sum_erase (Finset.univ.erase even) g (a := odd)
        (by simp [Ne.symm hne])]
      rw [Finset.sum_eq_zero (fun x hx => by
        have hx' := Finset.mem_erase.mp hx
        simp [g, v, (Finset.mem_erase.mp hx'.2).1, hx'.1])]
      simp [g, v, hdiagEven, hcross, hne, Ne.symm hne]
      ring
    have hodd : (sixVertexSectorTransfer N n c *ᵥ v) odd =
        c ^ (2 * n) - 2 := by
      rw [Matrix.mulVec, dotProduct]
      have hcross' : sixVertexSectorTransfer N n c odd even =
          c ^ (2 * n) := by
        calc
          sixVertexSectorTransfer N n c odd even =
              sixVertexSectorTransfer N n c even odd :=
            sixVertexTransfer_symmetric N c
              (sixVertexSectorRow odd) (sixVertexSectorRow even)
          _ = c ^ (2 * n) := hcross
      let g : SixVertexSector N n → Real := fun x =>
        sixVertexSectorTransfer N n c odd x * v x
      change ∑ x, g x = c ^ (2 * n) - 2
      rw [← Finset.add_sum_erase Finset.univ g (a := even)
        (Finset.mem_univ even)]
      rw [← Finset.add_sum_erase (Finset.univ.erase even) g (a := odd)
        (by simp [Ne.symm hne])]
      rw [Finset.sum_eq_zero (fun x hx => by
        have hx' := Finset.mem_erase.mp hx
        simp [g, v, (Finset.mem_erase.mp hx'.2).1, hx'.1])]
      simp [g, v, hdiagOdd, hcross', hne, Ne.symm hne]
      ring
    change f even + (f odd + ∑ x ∈ (Finset.univ.erase even).erase odd,
      f x) = 2 * (2 - c ^ (2 * n))
    simp only [f, v, heven, hodd]
    have hother (x : SixVertexSector N n) (hxe : x ≠ even)
        (hxo : x ≠ odd) : v x = 0 := by simp [v, hxe, hxo]
    rw [Finset.sum_eq_zero]
    · simp [hne, Ne.symm hne]
      ring
    · intro x hx
      have hx' := Finset.mem_erase.mp hx
      simp [v, (Finset.mem_erase.mp hx'.2).1, hx'.1]
  change (∑ x, v x * (sixVertexSectorTransfer N n c *ᵥ v) x) /
      (∑ x, v x ^ 2) = 2 - c ^ (2 * n)
  rw [hnum, hden]
  ring




theorem tendsto_sixVertexSectorTransfer_alternatingDifference_rayleigh_half
    {n : Nat} (hn : 0 < n) :
    Tendsto (fun c : Real => (2 - c ^ (2 * n)) / (c ^ 2 - 2) ^ n)
      atTop (nhds (-1)) := by
  have hzero := tendsto_sixVertexAnisotropyPowerRatio
    (d := 0) (n := n) (by omega)
  have hone := tendsto_sixVertexAnisotropyPowerRatio
    (d := 2 * n) (n := n) (le_rfl)
  have htwo : Tendsto (fun _ : Real => (2 : Real)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hsub := (htwo.mul hzero).sub hone
  have hsub' : Tendsto (fun c : Real =>
      2 * (c ^ 0 / (c ^ 2 - 2) ^ n) -
        c ^ (2 * n) / (c ^ 2 - 2) ^ n) atTop (nhds (-1)) := by
    simpa [hn.ne'] using hsub
  have heq : (fun c : Real =>
      2 * (c ^ 0 / (c ^ 2 - 2) ^ n) -
        c ^ (2 * n) / (c ^ 2 - 2) ^ n) =ᶠ[atTop]
      (fun c : Real => (2 - c ^ (2 * n)) / (c ^ 2 - 2) ^ n) :=
    Filter.Eventually.of_forall fun c => by
      simp only [pow_zero]
      ring
  exact hsub'.congr' heq



theorem exists_sixVertexSectorTransferNormalized_eigenvalue_le_alternating
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n = N) {c : Real}
    (hscale : (c ^ 2 - 2) ^ n ≠ 0) :
    ∃ μ : Real,
      Module.End.HasEigenvalue
        (Matrix.toEuclideanLin
          (sixVertexSectorTransferNormalized N n c)) μ ∧
      μ ≤ (2 - c ^ (2 * n)) / (c ^ 2 - 2) ^ n := by
  classical
  let even := sixVertexAlternatingEvenSector N n hhalf.le
  let odd := sixVertexAlternatingOddSector N n hhalf.le
  let w : SixVertexSector N n → Real := fun x =>
    if x = even then 1 else if x = odd then -1 else 0
  let v : EuclideanSpace Real (SixVertexSector N n) := WithLp.toLp 2 w
  letI : Nonempty (SixVertexSector N n) :=
    sixVertexSector_nonempty (by omega)
  have hv : v ≠ 0 := by
    intro h
    have heven := congrArg
      (fun z : EuclideanSpace Real (SixVertexSector N n) => z even) h
    simp [v, w] at heven
  obtain ⟨μ, hμ, hμle⟩ := exists_eigenvalue_le_rayleigh
    (sixVertexSectorTransferNormalized N n c)
    (sixVertexSectorTransferNormalized_isHermitian N n c) v hv
  refine ⟨μ, hμ, hμle.trans_eq ?_⟩
  have hden : (∑ x, w x ^ 2) = 2 := by
    let hne : even ≠ odd :=
      (sixVertexInfinityGraph_adj_alternating_of_half hn hhalf).ne
    rw [← Finset.add_sum_erase Finset.univ (fun x => w x ^ 2) (a := even)
      (Finset.mem_univ even)]
    rw [← Finset.add_sum_erase (Finset.univ.erase even)
      (fun x => w x ^ 2) (a := odd) (by simp [Ne.symm hne])]
    rw [Finset.sum_eq_zero (fun x hx => by
      have hx' := Finset.mem_erase.mp hx
      simp [w, (Finset.mem_erase.mp hx'.2).1, hx'.1])]
    norm_num [w, hne, Ne.symm hne]
  have hraw := sixVertexSectorTransfer_alternatingDifference_rayleigh
    hn hhalf c
  change (∑ x, w x * (sixVertexSectorTransfer N n c *ᵥ w) x) /
      (∑ x, w x ^ 2) = 2 - c ^ (2 * n) at hraw
  rw [hden] at hraw
  have hrawNum :
      (∑ x, w x * (sixVertexSectorTransfer N n c *ᵥ w) x) =
        2 * (2 - c ^ (2 * n)) := by
    linarith
  have hnormalizedNum :
      (∑ x, (sixVertexSectorTransferNormalized N n c *ᵥ w) x * w x) =
        (∑ x, w x * (sixVertexSectorTransfer N n c *ᵥ w) x) /
          (c ^ 2 - 2) ^ n := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
    have hinner :
        (∑ i, sixVertexSectorTransferNormalized N n c x i * w i) =
          (∑ i, sixVertexSectorTransfer N n c x i * w i) /
            (c ^ 2 - 2) ^ n := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      unfold sixVertexSectorTransferNormalized
      ring
    rw [hinner]
    ring
  rw [EuclideanSpace.inner_eq_star_dotProduct,
    EuclideanSpace.real_norm_sq_eq]
  simp only [Matrix.ofLp_toLpLin, star_trivial, dotProduct, v,
    WithLp.ofLp_toLp, Matrix.toLin'_apply, RCLike.re_to_real]
  change (∑ x, w x * (sixVertexSectorTransferNormalized N n c *ᵥ w) x) /
      (∑ x, w x ^ 2) = _
  have hcomm :
      (∑ x, w x * (sixVertexSectorTransferNormalized N n c *ᵥ w) x) =
        ∑ x, (sixVertexSectorTransferNormalized N n c *ᵥ w) x * w x := by
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hcomm]
  rw [hnormalizedNum, hrawNum, hden]
  field_simp [hscale]





theorem eventually_eq_sixVertexSectorTop_normalized_of_positive_eigenvalue_half
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n = N)
    (μ : Real → Real) {δ : Real} (hδ : 0 < δ)
    (hμeig : ∀ᶠ c : Real in atTop,
      Module.End.HasEigenvalue
        (Matrix.toEuclideanLin
          (sixVertexSectorTransferNormalized N n c)) (μ c))
    (hμlower : ∀ᶠ c : Real in atTop, δ ≤ μ c) :
    ∀ᶠ c : Real in atTop,
      μ c = sixVertexSectorTopEigenvalue N n (by omega) c /
        (c ^ 2 - 2) ^ n := by
  let ε : Real := min (1 / 4 : Real) (δ ^ 2 / 16)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεquarter : ε ≤ 1 / 4 := min_le_left _ _
  have hεδ : ε ≤ δ ^ 2 / 16 := min_le_right _ _
  have htrace := tendsto_trace_sixVertexSectorTransferNormalized_sq_half
    hn hhalf
  have htop := tendsto_sixVertexSectorTop_normalized_atTop_half hn hhalf
  have hray :=
    tendsto_sixVertexSectorTransfer_alternatingDifference_rayleigh_half hn
  have htraceEventually : ∀ᶠ c : Real in atTop,
      Matrix.trace (sixVertexSectorTransferNormalized N n c ^ 2) <
        2 + δ ^ 2 / 2 :=
    htrace.eventually_lt_const (by nlinarith [sq_pos_of_pos hδ])
  have htopEventually : ∀ᶠ c : Real in atTop,
      1 - ε < sixVertexSectorTopEigenvalue N n (by omega) c /
        (c ^ 2 - 2) ^ n :=
    htop.eventually_const_lt (by linarith)
  have hrayEventually : ∀ᶠ c : Real in atTop,
      (2 - c ^ (2 * n)) / (c ^ 2 - 2) ^ n < -1 + ε :=
    hray.eventually_lt_const (by linarith)
  filter_upwards [hμeig, hμlower, htraceEventually, htopEventually,
    hrayEventually, eventually_gt_atTop (2 : Real)] with
      c hcEig hcLower hcTrace hcTop hcRay hc
  have hscalePos : 0 < (c ^ 2 - 2) ^ n := pow_pos (by nlinarith) n
  have hscale : (c ^ 2 - 2) ^ n ≠ 0 := hscalePos.ne'
  let top : Real := sixVertexSectorTopEigenvalue N n (by omega) c /
    (c ^ 2 - 2) ^ n
  have htopEig : Module.End.HasEigenvalue
      (Matrix.toEuclideanLin
        (sixVertexSectorTransferNormalized N n c)) top := by
    exact sixVertexSectorTransferNormalized_top_hasEigenvalue
      (by omega) hscale
  obtain ⟨ν, hνeig, hνle⟩ :=
    exists_sixVertexSectorTransferNormalized_eigenvalue_le_alternating
      hn hhalf hscale
  have hνneg : ν < 0 := by
    dsimp only [ε] at hcRay ⊢
    have hεlt : ε < 1 := lt_of_le_of_lt hεquarter (by norm_num)
    linarith
  have htopPos : 0 < top := by
    have hεlt : ε < 1 := lt_of_le_of_lt hεquarter (by norm_num)
    dsimp only [top]
    linarith
  have hμpos : 0 < μ c := hδ.trans_le hcLower
  by_contra hne
  letI : Nonempty (SixVertexSector N n) :=
    sixVertexSector_nonempty (by omega)
  have htopmu : top ≠ μ c := by
    intro h
    apply hne
    exact h.symm
  have htopnu : top ≠ ν := by
    nlinarith
  have hmunu : μ c ≠ ν := by
    nlinarith
  have htraceLower := hermitian_three_eigenvalues_sq_le_trace_sq
    (sixVertexSectorTransferNormalized N n c)
    (sixVertexSectorTransferNormalized_isHermitian N n c)
    htopEig hcEig hνeig htopmu htopnu hmunu
  have htopSq : (1 - ε) ^ 2 < top ^ 2 := by
    nlinarith
  have hνSq : (1 - ε) ^ 2 < ν ^ 2 := by
    have hνbound : ν < -(1 - ε) := by
      linarith
    nlinarith
  have hμSq : δ ^ 2 ≤ (μ c) ^ 2 := by
    nlinarith
  have hbudget : 2 + δ ^ 2 / 2 <
      2 * (1 - ε) ^ 2 + δ ^ 2 := by
    nlinarith [sq_nonneg ε, sq_pos_of_pos hδ]
  dsimp only [top] at htraceLower htopSq
  nlinarith

end

end StatMech.FrontierD
