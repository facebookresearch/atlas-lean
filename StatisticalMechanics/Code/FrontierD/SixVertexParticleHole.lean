/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexPerron

open Finset Matrix

namespace StatMech.FrontierD

private theorem zip_map_same_particleHole {ι α β : Type*}
    (l : List ι) (f : ι → α) (g : ι → β) :
    (l.map f).zip (l.map g) = l.map fun i => (f i, g i) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem pairwise_flatMap_pairs_elim {ι α : Type*} [Preorder α]
    (f g : ι → α) {l : List ι}
    (h : (l.flatMap fun i => [f i, g i]).Pairwise (· ≤ ·)) :
    (∀ i ∈ l, f i ≤ g i) ∧ l.Pairwise (fun i j => g i ≤ f j) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      change List.Pairwise (· ≤ ·)
        (f a :: g a :: (l.flatMap fun i => [f i, g i])) at h
      rw [List.pairwise_cons_cons_iff_of_trans] at h
      obtain ⟨hsame, htail⟩ := h
      rw [List.pairwise_cons] at htail
      obtain ⟨hcross, hrest⟩ := htail
      obtain ⟨ihsame, ihcross⟩ := ih hrest
      constructor
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact hsame
        · exact ihsame i hi
      · rw [List.pairwise_cons]
        refine ⟨?_, ihcross⟩
        intro j hj
        apply hcross (f j)
        exact List.mem_flatMap.mpr ⟨j, hj, by simp⟩

theorem sixVertexPositionsForwardInterlaced_of_forward {N n : ℕ}
    (x y : SixVertexSector N n)
    (h : SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y)) :
    SixVertexPositionsForwardInterlaced x y := by
  rw [SixVertexForwardInterlaced] at h
  rw [sixVertexAlternating, sixVertexSector_upPositions_eq_map_position,
    sixVertexSector_upPositions_eq_map_position, zip_map_same_particleHole] at h
  simp only [List.flatMap_map] at h
  obtain ⟨hsame, hcross⟩ := pairwise_flatMap_pairs_elim
    (sixVertexSectorPosition x) (sixVertexSectorPosition y) h.2
  constructor
  · intro i
    exact hsame i (by simp)
  · intro k hk
    have hrel := (List.pairwise_iff_getElem.mp hcross) k (k + 1)
      (by simp; omega) (by simp; omega) (by omega)
    simpa using hrel


def sixVertexSectorPrefixCount {N n : ℕ}
    (x : SixVertexSector N n) (k : Fin N) : ℕ :=
  #{j ∈ (x : Finset (Fin N)) | j ≤ k}

private theorem sixVertexSectorPrefixCount_at_position {N n : ℕ}
    (x : SixVertexSector N n) (i : Fin n) :
    sixVertexSectorPrefixCount x (sixVertexSectorPosition x i) = i.val + 1 := by
  let f := sixVertexSectorPosition x
  have heq : ({j ∈ (x : Finset (Fin N)) | j ≤ f i} : Finset (Fin N)) =
      Finset.image f (Finset.Iic i) := by
    ext j
    constructor
    · intro hj
      simp only [Finset.mem_filter] at hj
      have hjrange : j ∈ Set.range f := by
        rw [show Set.range f = (x.val : Set (Fin N)) by
          change Set.range (x.val.orderEmbOfFin x.prop) = _
          exact Finset.range_orderEmbOfFin x.val x.prop]
        exact hj.1
      obtain ⟨q, rfl⟩ := hjrange
      exact Finset.mem_image.mpr
        ⟨q, Finset.mem_Iic.mpr ((f.le_iff_le).mp hj.2), rfl⟩
    · intro hj
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_filter.mpr
        ⟨sixVertexSectorPosition_mem x q,
          (f.le_iff_le).mpr (Finset.mem_Iic.mp hq)⟩
  rw [sixVertexSectorPrefixCount, heq,
    Finset.card_image_of_injective _ f.injective, Fin.card_Iic]

private theorem sixVertexSectorPrefixCount_strict_position {N n : ℕ}
    (x : SixVertexSector N n) (i : Fin n) :
    #{j ∈ (x : Finset (Fin N)) | j < sixVertexSectorPosition x i} = i.val := by
  let f := sixVertexSectorPosition x
  have heq : ({j ∈ (x : Finset (Fin N)) | j < f i} : Finset (Fin N)) =
      Finset.image f (Finset.Iio i) := by
    ext j
    constructor
    · intro hj
      simp only [Finset.mem_filter] at hj
      have hjrange : j ∈ Set.range f := by
        rw [show Set.range f = (x.val : Set (Fin N)) by
          change Set.range (x.val.orderEmbOfFin x.prop) = _
          exact Finset.range_orderEmbOfFin x.val x.prop]
        exact hj.1
      obtain ⟨q, rfl⟩ := hjrange
      exact Finset.mem_image.mpr
        ⟨q, Finset.mem_Iio.mpr ((f.lt_iff_lt).mp hj.2), rfl⟩
    · intro hj
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_filter.mpr
        ⟨sixVertexSectorPosition_mem x q,
          (f.lt_iff_lt).mpr (Finset.mem_Iio.mp hq)⟩
  rw [heq, Finset.card_image_of_injective _ f.injective, Fin.card_Iio]

theorem sixVertexSectorPosition_le_iff_lt_prefixCount {N n : ℕ}
    (x : SixVertexSector N n) (i : Fin n) (k : Fin N) :
    sixVertexSectorPosition x i ≤ k ↔
      i.val < sixVertexSectorPrefixCount x k := by
  constructor
  · intro hik
    rw [← Nat.add_one_le_iff,
      ← sixVertexSectorPrefixCount_at_position x i]
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, hj.2.trans hik⟩
  · intro hcard
    by_contra! hnot
    have hle : sixVertexSectorPrefixCount x k ≤ i.val := by
      rw [← sixVertexSectorPrefixCount_strict_position x i]
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, hj.2.trans_lt hnot⟩
    omega

private theorem sixVertexSectorPrefixCount_le_card {N n : ℕ}
    (x : SixVertexSector N n) (k : Fin N) :
    sixVertexSectorPrefixCount x k ≤ n := by
  calc
    sixVertexSectorPrefixCount x k ≤ (x : Finset (Fin N)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := x.prop


def SixVertexSectorPrefixForward {N n : ℕ}
    (x y : SixVertexSector N n) : Prop :=
  ∀ k, sixVertexSectorPrefixCount y k ≤ sixVertexSectorPrefixCount x k ∧
    sixVertexSectorPrefixCount x k ≤ sixVertexSectorPrefixCount y k + 1

theorem sixVertexSectorPrefixForward_of_positions {N n : ℕ}
    (x y : SixVertexSector N n) (h : SixVertexPositionsForwardInterlaced x y) :
    SixVertexSectorPrefixForward x y := by
  intro k
  let px := sixVertexSectorPrefixCount x k
  let py := sixVertexSectorPrefixCount y k
  constructor
  · by_contra! hbad
    have hpyn : py ≤ n := sixVertexSectorPrefixCount_le_card y k
    let i : Fin n := ⟨px, lt_of_lt_of_le hbad hpyn⟩
    have hyk : sixVertexSectorPosition y i ≤ k := by
      apply (sixVertexSectorPosition_le_iff_lt_prefixCount y i k).mpr
      exact hbad
    have hxk : sixVertexSectorPosition x i ≤ k := (h.1 i).trans hyk
    have := (sixVertexSectorPosition_le_iff_lt_prefixCount x i k).mp hxk
    exact (Nat.lt_irrefl px) this
  · by_contra! hbad
    have hpxn : px ≤ n := sixVertexSectorPrefixCount_le_card x k
    have hpylt : py + 1 < n := lt_of_lt_of_le hbad hpxn
    let i : Fin n := ⟨py + 1, hpylt⟩
    have hxk : sixVertexSectorPosition x i ≤ k := by
      apply (sixVertexSectorPosition_le_iff_lt_prefixCount x i k).mpr
      exact hbad
    have hcross := h.2 py (by omega)
    have hyk : sixVertexSectorPosition y ⟨py, by omega⟩ ≤ k := by
      exact hcross.trans hxk
    have := (sixVertexSectorPosition_le_iff_lt_prefixCount y
      ⟨py, by omega⟩ k).mp hyk
    exact (Nat.lt_irrefl py) this

theorem sixVertexPositionsForwardInterlaced_of_prefix {N n : ℕ}
    (x y : SixVertexSector N n) (h : SixVertexSectorPrefixForward x y) :
    SixVertexPositionsForwardInterlaced x y := by
  constructor
  · intro i
    let k := sixVertexSectorPosition y i
    apply (sixVertexSectorPosition_le_iff_lt_prefixCount x i k).mpr
    have hy : sixVertexSectorPrefixCount y k = i.val + 1 :=
      sixVertexSectorPrefixCount_at_position y i
    have hle := (h k).1
    omega
  · intro k hk
    let i : Fin n := ⟨k + 1, hk⟩
    let p := sixVertexSectorPosition x i
    apply (sixVertexSectorPosition_le_iff_lt_prefixCount y ⟨k, by omega⟩ p).mpr
    have hx : sixVertexSectorPrefixCount x p = k + 2 := by
      simpa [i] using sixVertexSectorPrefixCount_at_position x i
    have hle := (h p).2
    change k < sixVertexSectorPrefixCount y p
    omega


def sixVertexSectorComplement {N n : ℕ}
    (x : SixVertexSector N n) : SixVertexSector N (N - n) :=
  ⟨(x : Finset (Fin N))ᶜ, by simp [Finset.card_compl]⟩


def sixVertexSectorParticleHoleEquiv (N n : ℕ) (hn : n ≤ N) :
    SixVertexSector N n ≃ SixVertexSector N (N - n) where
  toFun := sixVertexSectorComplement
  invFun y := ⟨(y : Finset (Fin N))ᶜ, by
    have hy := y.prop
    change ((y : Finset (Fin N))ᶜ).card = n
    change (y : Finset (Fin N)).card = N - n at hy
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega⟩
  left_inv x := by
    apply Subtype.ext
    simp [sixVertexSectorComplement]
  right_inv y := by
    apply Subtype.ext
    simp [sixVertexSectorComplement]

@[simp] theorem sixVertexSectorParticleHoleEquiv_apply_val
    {N n : ℕ} (hn : n ≤ N) (x : SixVertexSector N n) :
    ((sixVertexSectorParticleHoleEquiv N n hn x : SixVertexSector N (N - n)) :
      Finset (Fin N)) = (x : Finset (Fin N))ᶜ :=
  rfl

@[simp] theorem sixVertexSectorRow_particleHole {N n : ℕ} (hn : n ≤ N)
    (x : SixVertexSector N n) (i : Fin N) :
    sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn x) i =
      !sixVertexSectorRow x i := by
  simp [sixVertexSectorRow]

theorem sixVertexSectorPrefixCount_add_complement {N n : ℕ}
    (x : SixVertexSector N n) (k : Fin N) :
    sixVertexSectorPrefixCount x k +
      sixVertexSectorPrefixCount (sixVertexSectorComplement x) k = k.val + 1 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.Iic k) (fun j : Fin N => j ∈ (x : Finset (Fin N)))
  have hfirst :
      (Finset.Iic k).filter (fun j => j ∈ (x : Finset (Fin N))) =
        (x : Finset (Fin N)).filter (fun j => j ≤ k) := by
    ext j
    simp [and_comm]
  have hsecond :
      (Finset.Iic k).filter (fun j => ¬j ∈ (x : Finset (Fin N))) =
        ((sixVertexSectorComplement x : SixVertexSector N (N - n)) :
          Finset (Fin N)).filter (fun j => j ≤ k) := by
    ext j
    simp [sixVertexSectorComplement, and_comm]
  rw [hfirst, hsecond, Fin.card_Iic] at h
  exact h

theorem sixVertexSectorPrefixForward_complement {N n : ℕ}
    (x y : SixVertexSector N n) (h : SixVertexSectorPrefixForward x y) :
    SixVertexSectorPrefixForward (sixVertexSectorComplement y)
      (sixVertexSectorComplement x) := by
  intro k
  have hx := sixVertexSectorPrefixCount_add_complement x k
  have hy := sixVertexSectorPrefixCount_add_complement y k
  have hxy := h k
  omega

theorem sixVertexSectorPrefixForward_particleHole_iff {N n : ℕ}
    (hn : n ≤ N) (x y : SixVertexSector N n) :
    SixVertexSectorPrefixForward
        (sixVertexSectorParticleHoleEquiv N n hn y)
        (sixVertexSectorParticleHoleEquiv N n hn x) ↔
      SixVertexSectorPrefixForward x y := by
  change SixVertexSectorPrefixForward (sixVertexSectorComplement y)
      (sixVertexSectorComplement x) ↔ SixVertexSectorPrefixForward x y
  constructor
  · intro h k
    have hx := sixVertexSectorPrefixCount_add_complement x k
    have hy := sixVertexSectorPrefixCount_add_complement y k
    have hxy := h k
    omega
  · exact sixVertexSectorPrefixForward_complement x y

theorem sixVertexInterlaced_particleHole_imp {N n : ℕ} (hn : n ≤ N)
    (x y : SixVertexSector N n)
    (h : SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y)) :
    SixVertexInterlaced
      (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn x))
      (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn y)) := by
  rcases h with hxy | hyx
  · right
    apply sixVertexForwardInterlaced_of_positions
    apply sixVertexPositionsForwardInterlaced_of_prefix
    exact sixVertexSectorPrefixForward_complement x y
      (sixVertexSectorPrefixForward_of_positions x y
        (sixVertexPositionsForwardInterlaced_of_forward x y hxy))
  · left
    apply sixVertexForwardInterlaced_of_positions
    apply sixVertexPositionsForwardInterlaced_of_prefix
    exact sixVertexSectorPrefixForward_complement y x
      (sixVertexSectorPrefixForward_of_positions y x
        (sixVertexPositionsForwardInterlaced_of_forward y x hyx))

theorem sixVertexInterlaced_particleHole_iff {N n : ℕ} (hn : n ≤ N)
    (x y : SixVertexSector N n) :
    SixVertexInterlaced
        (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn x))
        (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn y)) ↔
      SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) := by
  constructor
  · intro h
    rcases h with hxy | hyx
    · right
      apply sixVertexForwardInterlaced_of_positions
      apply sixVertexPositionsForwardInterlaced_of_prefix
      apply (sixVertexSectorPrefixForward_particleHole_iff hn y x).mp
      exact sixVertexSectorPrefixForward_of_positions _ _
        (sixVertexPositionsForwardInterlaced_of_forward _ _ hxy)
    · left
      apply sixVertexForwardInterlaced_of_positions
      apply sixVertexPositionsForwardInterlaced_of_prefix
      apply (sixVertexSectorPrefixForward_particleHole_iff hn x y).mp
      exact sixVertexSectorPrefixForward_of_positions _ _
        (sixVertexPositionsForwardInterlaced_of_forward _ _ hyx)
  · exact sixVertexInterlaced_particleHole_imp hn x y

theorem sixVertexRowDistance_particleHole {N n : ℕ} (hn : n ≤ N)
    (x y : SixVertexSector N n) :
    sixVertexRowDistance
        (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn x))
        (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn y)) =
      sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) := by
  unfold sixVertexRowDistance
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    sixVertexSectorRow_particleHole]
  cases sixVertexSectorRow x i <;> cases sixVertexSectorRow y i <;> decide

theorem sixVertexSectorRow_injective {N n : ℕ} :
    Function.Injective (@sixVertexSectorRow N n) := by
  intro x y h
  apply Subtype.ext
  ext i
  have hi := congrFun h i
  simp only [sixVertexSectorRow_apply] at hi
  simpa using hi

theorem sixVertexSectorTransfer_particleHole {N n : ℕ} (hn : n ≤ N)
    (c : ℝ) (x y : SixVertexSector N n) :
    sixVertexSectorTransfer N (N - n) c
        (sixVertexSectorParticleHoleEquiv N n hn x)
        (sixVertexSectorParticleHoleEquiv N n hn y) =
      sixVertexSectorTransfer N n c x y := by
  let e := sixVertexSectorParticleHoleEquiv N n hn
  have heinj : Function.Injective
      (fun x : SixVertexSector N n => sixVertexSectorRow (e x)) :=
    sixVertexSectorRow_injective.comp e.injective
  by_cases hxy : x = y
  · subst y
    simp [sixVertexSectorTransfer, sixVertexTransfer]
  · have hexy : sixVertexSectorRow (e x) ≠ sixVertexSectorRow (e y) := by
      intro h
      exact hxy (heinj h)
    have hrowxy : sixVertexSectorRow x ≠ sixVertexSectorRow y := by
      intro h
      exact hxy (sixVertexSectorRow_injective h)
    simp only [sixVertexSectorTransfer, sixVertexTransfer_apply]
    rw [if_neg hrowxy, if_neg hexy]
    by_cases hinter : SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y)
    · have hinter' := (sixVertexInterlaced_particleHole_iff hn x y).mpr hinter
      simp [hinter, hinter', sixVertexRowDistance_particleHole hn x y]
    · have hinter' : ¬SixVertexInterlaced
          (sixVertexSectorRow (e x)) (sixVertexSectorRow (e y)) := by
        exact fun h => hinter ((sixVertexInterlaced_particleHole_iff hn x y).mp h)
      change ¬SixVertexInterlaced
        (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn x))
        (sixVertexSectorRow (sixVertexSectorParticleHoleEquiv N n hn y)) at hinter'
      simp [hinter, hinter']

theorem sixVertexSectorTransfer_reindex_particleHole {N n : ℕ} (hn : n ≤ N)
    (c : ℝ) :
    Matrix.reindex (sixVertexSectorParticleHoleEquiv N n hn)
        (sixVertexSectorParticleHoleEquiv N n hn)
        (sixVertexSectorTransfer N n c) =
      sixVertexSectorTransfer N (N - n) c := by
  let e := sixVertexSectorParticleHoleEquiv N n hn
  ext x y
  rw [Matrix.reindex_apply]
  change sixVertexSectorTransfer N n c (e.symm x) (e.symm y) = _
  rw [← sixVertexSectorTransfer_particleHole hn c (e.symm x) (e.symm y)]
  simp [e]

private theorem matrix_hasEigenvalue_of_equiv
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (A : Matrix α α ℝ) (B : Matrix β β ℝ)
    (hentry : ∀ x y, B (e x) (e y) = A x y) {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) μ) :
    Module.End.HasEigenvalue (Matrix.toEuclideanLin B) μ := by
  classical
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hveig : A *ᵥ (fun i => v i) = μ • (fun i => v i) := by
    have hvT := Module.End.mem_eigenspace_iff.mp hv.1
    have hvT' := congrArg WithLp.ofLp hvT
    simpa [Matrix.ofLp_toLpLin] using hvT'
  let w : EuclideanSpace ℝ β := WithLp.toLp 2 fun j => v (e.symm j)
  have hwne : w ≠ 0 := by
    intro hw0
    apply hv.2
    apply WithLp.ofLp_injective 2
    funext i
    have hi := congrArg (fun q : EuclideanSpace ℝ β => q (e i)) hw0
    simpa [w] using hi
  have hweig : B *ᵥ (fun j => w j) = μ • (fun j => w j) := by
    funext j
    have hvj := congrFun hveig (e.symm j)
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hvj ⊢
    calc
      ∑ z, B j z * w z = ∑ i, B j (e i) * v i := by
        symm
        apply Fintype.sum_equiv e
        intro i
        simp [w]
      _ = ∑ i, A (e.symm j) i * v i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hentry]
        simp
      _ = μ * v (e.symm j) := hvj
      _ = μ * w j := by simp [w]
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hwne⟩
  apply WithLp.ofLp_injective 2
  simpa [Matrix.ofLp_toLpLin] using hweig

private theorem sixVertexSectorTop_ge_of_hasEigenvalue {N n : ℕ} (hn : n ≤ N)
    (c μ : ℝ)
    (hμ : Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)) μ) :
    μ ≤ sixVertexSectorTopEigenvalue N n hn c := by
  classical
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hn
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (sixVertexSectorTransfer_isHermitian N n c)
  obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq finrank_euclideanSpace hμ
  rw [← hi]
  exact sixVertexSectorTopEigenvalue_ge N n hn c i


theorem sixVertexSectorTopEigenvalue_particleHole {N n : ℕ} (hn : n ≤ N)
    (c : ℝ) :
    sixVertexSectorTopEigenvalue N (N - n) (Nat.sub_le N n) c =
      sixVertexSectorTopEigenvalue N n hn c := by
  let e := sixVertexSectorParticleHoleEquiv N n hn
  let A := sixVertexSectorTransfer N n c
  let B := sixVertexSectorTransfer N (N - n) c
  apply le_antisymm
  · apply sixVertexSectorTop_ge_of_hasEigenvalue hn
    apply matrix_hasEigenvalue_of_equiv e.symm B A
    · intro x y
      have h := sixVertexSectorTransfer_particleHole hn c (e.symm x) (e.symm y)
      simpa [e] using h.symm
    · exact sixVertexSectorTop_hasEigenvalue N (N - n) (Nat.sub_le N n) c
  · apply sixVertexSectorTop_ge_of_hasEigenvalue (Nat.sub_le N n)
    apply matrix_hasEigenvalue_of_equiv e A B
    · exact sixVertexSectorTransfer_particleHole hn c
    · exact sixVertexSectorTop_hasEigenvalue N n hn c

private theorem sixVertex_half_add_le {N r : ℕ} (hN : Even N)
    (hr : r ≤ N / 2) : N / 2 + r ≤ N := by
  obtain ⟨k, rfl⟩ := hN
  omega



noncomputable def sixVertexLambdaNeg (N r : ℕ) (hN : Even N)
    (hr : r ≤ N / 2) (c : ℝ) : ℝ :=
  sixVertexSectorTopEigenvalue N (N / 2 + r) (sixVertex_half_add_le hN hr) c

private theorem sixVertexSectorTopEigenvalue_congr_index
    {N a b : ℕ} (hab : a = b) (ha : a ≤ N) (hb : b ≤ N) (c : ℝ) :
    sixVertexSectorTopEigenvalue N a ha c =
      sixVertexSectorTopEigenvalue N b hb c := by
  subst b
  rfl


theorem sixVertexLambda_particleHole (N r : ℕ) (hN : Even N)
    (hr : r ≤ N / 2) (c : ℝ) :
    sixVertexLambdaNeg N r hN hr c = sixVertexLambda N r hN hr c := by
  let hn : N / 2 - r ≤ N := (Nat.sub_le _ _).trans (Nat.div_le_self N 2)
  have h := sixVertexSectorTopEigenvalue_particleHole hn c
  obtain ⟨k, hk⟩ := hN
  subst N
  have hidx : k + k - ((k + k) / 2 - r) = (k + k) / 2 + r := by omega
  unfold sixVertexLambdaNeg sixVertexLambda
  convert h using 1
  exact sixVertexSectorTopEigenvalue_congr_index hidx.symm _ _ c

end StatMech.FrontierD
