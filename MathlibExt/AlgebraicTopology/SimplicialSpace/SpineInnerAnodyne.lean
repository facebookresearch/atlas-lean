/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalizingMaps
public import Mathlib.Order.Fin.InsertNth
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerAnodyneCategorical

/-!
# Inner anodyneness of simplex spines

For `2 ≤ n`, the consecutive-edge spine `G(n)` inside `Δ[n]` is inner
anodyne. The proof uses Mathlib's native regular-pairing API. A type-II
simplex is a nondegenerate simplex outside the spine whose first two vertices
have a gap. Its paired type-I simplex inserts the missing successor of the
first vertex. The distinguished face has index `1`, hence is inner.

Regularity follows from a weak rank given by the span between the first and
last vertices. Among ancestral simplices of the same dimension, deleting the
inserted vertex gives the original type-II simplex, deleting the first vertex
strictly decreases the span, and deleting any later vertex leaves the first
two vertices consecutive and therefore cannot produce a type-II simplex.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet.Rezk

namespace spinePairing

variable (n : ℕ)

private instance : HasDimensionLE (spineSubcomplex.{u} n : SSet.{u}) 1 := by
  change HasDimensionLT (spineSubcomplex.{u} n : SSet.{u}) 2
  rw [spineSubcomplex, hasDimensionLT_iSup_iff]
  intro i
  infer_instance

private lemma mem_spineSubcomplex_iff {d : ℕ}
    (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x ∈ (spineSubcomplex.{u} n).obj (op ⦋d⦌) ↔
      ∃ (i : Fin n) (f : ⦋d⦌ ⟶ ⦋1⦌),
        f ≫ SimplexCategory.mkOfSucc i = stdSimplex.objEquiv x := by
  simp only [spineSubcomplex, Subfunctor.iSup_obj, Set.mem_iUnion,
    Subfunctor.range_obj]
  constructor
  · rintro ⟨i, y, hy⟩
    refine ⟨i, stdSimplex.objEquiv y, ?_⟩
    apply stdSimplex.objEquiv.symm.injective
    rw [stdSimplex.objEquiv_symm_comp, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply]
    exact hy
  · rintro ⟨i, f, hf⟩
    refine ⟨i, stdSimplex.objEquiv.symm f, ?_⟩
    rw [← stdSimplex.objEquiv_symm_comp, hf,
      Equiv.symm_apply_apply]

private lemma vertex_mem (hn : 1 ≤ n) (x : (Δ[n] : SSet.{u}) _⦋0⦌) :
    x ∈ (spineSubcomplex.{u} n).obj (op ⦋0⦌) := by
  apply (mem_spineSubcomplex_iff n x).2
  let j := x (0 : Fin 1)
  by_cases hj : j.val < n
  · let i : Fin n := ⟨j.val, hj⟩
    refine ⟨i, SimplexCategory.const _ _ (0 : Fin 2), ?_⟩
    ext k
    fin_cases k
    change i.val = (x (0 : Fin 1)).val
    rfl
  · let i : Fin n := ⟨n - 1, by omega⟩
    refine ⟨i, SimplexCategory.const _ _ (1 : Fin 2), ?_⟩
    ext k
    fin_cases k
    change i.val + 1 = (x (0 : Fin 1)).val
    dsimp [i, j]
    have := (x (0 : Fin 1)).isLt
    omega

private lemma edge_mem_of_consecutive (x : (Δ[n] : SSet.{u}) _⦋1⦌)
    (h : (x (0 : Fin 2)).val + 1 = (x (1 : Fin 2)).val) :
    x ∈ (spineSubcomplex.{u} n).obj (op ⦋1⦌) := by
  apply (mem_spineSubcomplex_iff n x).2
  let i : Fin n := ⟨(x (0 : Fin 2)).val, by
    have := (x (1 : Fin 2)).isLt
    omega⟩
  refine ⟨i, 𝟙 _, ?_⟩
  ext k
  fin_cases k
  · change i.val = (x (0 : Fin 2)).val
    rfl
  · change i.val + 1 = (x (1 : Fin 2)).val
    dsimp [i]
    exact h

private lemma edge_consecutive_of_mem (x : (Δ[n] : SSet.{u}) _⦋1⦌)
    (hx : x ∈ (Δ[n] : SSet.{u}).nonDegenerate 1)
    (hmem : x ∈ (spineSubcomplex.{u} n).obj (op ⦋1⦌)) :
    (x (0 : Fin 2)).val + 1 = (x (1 : Fin 2)).val := by
  obtain ⟨i, f, hf⟩ := (mem_spineSubcomplex_iff n x).1 hmem
  have : Mono (stdSimplex.objEquiv x) :=
    (stdSimplex.mem_nonDegenerate_iff_mono x).1 hx
  let : Mono (f ≫ SimplexCategory.mkOfSucc i) := by
    rw [hf]
    infer_instance
  let : Mono f := mono_of_mono f (SimplexCategory.mkOfSucc i)
  obtain rfl := SimplexCategory.eq_id_of_mono f
  have hf' : SimplexCategory.mkOfSucc i = stdSimplex.objEquiv x := by
    simpa using hf
  have h0 := congrArg
    (fun q : ⦋1⦌ ⟶ ⦋n⦌ => q.toOrderHom (0 : Fin 2)) hf'
  have h1 := congrArg
    (fun q : ⦋1⦌ ⟶ ⦋n⦌ => q.toOrderHom (1 : Fin 2)) hf'
  change i.castSucc = x (0 : Fin 2) at h0
  change i.succ = x (1 : Fin 2) at h1
  rw [← h0, ← h1]
  rfl

private lemma not_mem_of_gap {d : ℕ} (hd : 0 < d)
    (x : (Δ[n] : SSet.{u}) _⦋d⦌)
    (hx : x ∈ (Δ[n] : SSet.{u}).nonDegenerate d)
    (hgap : (x (0 : Fin (d + 1))).val + 1 <
      (x (⟨1, Nat.succ_lt_succ hd⟩ : Fin (d + 1))).val) :
    x ∉ (spineSubcomplex.{u} n).obj (op ⦋d⦌) := by
  intro hmem
  have hnd : (⟨x, hmem⟩ : (spineSubcomplex.{u} n : SSet.{u}) _⦋d⦌) ∈
      (spineSubcomplex.{u} n : SSet.{u}).nonDegenerate d := by
    rw [Subcomplex.mem_nonDegenerate_iff]
    exact hx
  have hle : d ≤ 1 :=
    (spineSubcomplex.{u} n : SSet.{u}).dim_le_of_nonDegenerate ⟨_, hnd⟩ 1
  obtain rfl : d = 1 := by omega
  have hc := edge_consecutive_of_mem n x hx hmem
  have hgap' : (x (0 : Fin 2)).val + 1 < (x (1 : Fin 2)).val := by
    simpa using hgap
  omega

private lemma outside_dim_pos (hn : 1 ≤ n) (x : (spineSubcomplex.{u} n).N) :
    0 < x.dim := by
  by_contra h
  have hd : x.dim = 0 := by omega
  have hm := vertex_mem n hn (x.cast hd).simplex
  exact (x.cast hd).notMem hm

private structure Index where
  dim : ℕ
  simplex : (Δ[n] : SSet.{u}) _⦋dim⦌
  nonDegenerate : simplex ∈ (Δ[n] : SSet.{u}).nonDegenerate dim
  notMem : simplex ∉ (spineSubcomplex.{u} n).obj (op ⦋dim⦌)
  dim_pos : 0 < dim
  gap : (simplex (0 : Fin (dim + 1))).val + 1 <
    (simplex (⟨1, by omega⟩ : Fin (dim + 1))).val

private def Index.toN (s : Index.{u} n) : (spineSubcomplex.{u} n).N :=
  Subcomplex.N.mk s.simplex s.nonDegenerate s.notMem

@[ext]
private lemma Index.ext {s t : Index.{u} n}
    (h : SSet.S.mk s.simplex = SSet.S.mk t.simplex) : s = t := by
  cases s
  cases t
  cases h
  rfl

variable {n}

private def Index.i (s : Index.{u} n) : Fin s.dim := ⟨0, s.dim_pos⟩

private def Index.one (s : Index.{u} n) : Fin (s.dim + 1) :=
  ⟨1, Nat.succ_lt_succ s.dim_pos⟩

private def Index.pivot (s : Index.{u} n) : Fin (n + 1) :=
  ⟨(s.simplex (0 : Fin (s.dim + 1))).val + 1, by
    exact lt_trans s.gap (s.simplex s.one).isLt⟩

@[simp]
private lemma Index.pivot_val (s : Index.{u} n) :
    s.pivot.val = (s.simplex (0 : Fin (s.dim + 1))).val + 1 := rfl

private def Index.embedding (s : Index.{u} n) :
    Fin (s.dim + 2) ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono
    (Fin.insertNth s.i.castSucc.succ s.pivot s.simplex)
    (Fin.strictMono_insertNth
      ((stdSimplex.mem_nonDegenerate_iff_strictMono _).1 s.nonDegenerate)
      s.i s.pivot (by
        rw [Fin.mk_lt_mk]
        simp [Index.i, Index.pivot])
      (by
        rw [Fin.mk_lt_mk]
        simpa [Index.i, Index.one, Index.pivot] using s.gap))

private def Index.paired (s : Index.{u} n) :
    (Δ[n] : SSet.{u}).nonDegenerate (s.dim + 1) :=
  stdSimplex.nonDegenerateEquiv.symm s.embedding

private def Index.faceIndex (s : Index.{u} n) : Fin (s.dim + 2) :=
  s.i.castSucc.succ

@[simp]
private lemma Index.paired_apply (s : Index.{u} n) (j : Fin (s.dim + 2)) :
    s.paired.val j = s.embedding j := by
  simpa [Index.paired] using
    (stdSimplex.nonDegenerateEquiv_apply_apply s.paired j).symm

@[simp]
private lemma Index.paired_δ (s : Index.{u} n) :
    (Δ[n] : SSet.{u}).δ s.faceIndex s.paired.val = s.simplex := by
  apply stdSimplex.objEquiv.injective
  ext j
  simp [stdSimplex.δ_apply, Index.faceIndex, Index.embedding]

private lemma Index.paired_zero (s : Index.{u} n) :
    s.paired.val (0 : Fin (s.dim + 2)) =
      s.simplex (0 : Fin (s.dim + 1)) := by
  rw [Index.paired_apply]
  change (Fin.insertNth (α := fun _ => Fin (n + 1))
    s.faceIndex s.pivot s.simplex) 0 = _
  rw [Fin.insertNth_apply_below (by simp [Index.faceIndex, Index.i])]
  congr

private lemma Index.paired_faceIndex (s : Index.{u} n) :
    s.paired.val s.faceIndex = s.pivot := by
  rw [Index.paired_apply]
  simp [Index.embedding, Index.faceIndex]

private lemma Index.paired_last (s : Index.{u} n) :
    s.paired.val (Fin.last (s.dim + 1)) =
      s.simplex (Fin.last s.dim) := by
  have h := congrArg
    (fun z : (Δ[n] : SSet.{u}) _⦋s.dim⦌ => z (Fin.last s.dim)) s.paired_δ
  change s.paired.val (s.faceIndex.succAbove (Fin.last s.dim)) = _ at h
  rw [Fin.succAbove_ne_last_last] at h
  · exact h
  · intro heq
    have hval := congrArg Fin.val heq
    simp [Index.faceIndex, Index.i] at hval
    have := s.dim_pos
    omega

@[simp]
private lemma Index.embedding_zero (s : Index.{u} n) :
    s.embedding (0 : Fin (s.dim + 2)) =
      s.simplex (0 : Fin (s.dim + 1)) := by
  exact (s.paired_apply 0).symm.trans s.paired_zero

@[simp]
private lemma Index.embedding_faceIndex (s : Index.{u} n) :
    s.embedding s.faceIndex = s.pivot := by
  exact (s.paired_apply s.faceIndex).symm.trans s.paired_faceIndex

@[simp]
private lemma Index.embedding_last (s : Index.{u} n) :
    s.embedding (Fin.last (s.dim + 1)) =
      s.simplex (Fin.last s.dim) := by
  exact (s.paired_apply (Fin.last (s.dim + 1))).symm.trans s.paired_last

private lemma not_mem_of_two_le_dim {d : ℕ} (hd : 2 ≤ d)
    (x : (Δ[n] : SSet.{u}) _⦋d⦌)
    (hx : x ∈ (Δ[n] : SSet.{u}).nonDegenerate d) :
    x ∉ (spineSubcomplex.{u} n).obj (op ⦋d⦌) := by
  intro hmem
  have hnd : (⟨x, hmem⟩ : (spineSubcomplex.{u} n : SSet.{u}) _⦋d⦌) ∈
      (spineSubcomplex.{u} n : SSet.{u}).nonDegenerate d := by
    rw [Subcomplex.mem_nonDegenerate_iff]
    exact hx
  have hle : d ≤ 1 :=
    (spineSubcomplex.{u} n : SSet.{u}).dim_le_of_nonDegenerate ⟨_, hnd⟩ 1
  omega

private def unpair (z : (Δ[n] : SSet.{u}).S) : (Δ[n] : SSet.{u}).S :=
  match h : z.dim with
  | 0 => z
  | d + 1 => SSet.S.mk ((Δ[n] : SSet.{u}).δ
      (⟨1, by omega⟩ : Fin (d + 2)) (z.cast h).simplex)

@[simp]
private lemma unpair_paired (s : Index.{u} n) :
    unpair (SSet.S.mk s.paired.val) = SSet.S.mk s.simplex := by
  change SSet.S.mk ((Δ[n] : SSet.{u}).δ
    (⟨1, by omega⟩ : Fin (s.dim + 2)) s.paired.val) = _
  rw [SSet.S.ext_iff]
  simpa [Index.faceIndex, Index.i] using s.paired_δ

private def firstConsecutive (z : (Δ[n] : SSet.{u}).S) : Prop :=
  match h : z.dim with
  | 0 => False
  | d + 1 =>
      let x := (z.cast h).simplex
      (x (0 : Fin (d + 2))).val + 1 = (x (1 : Fin (d + 2))).val

private lemma firstConsecutive_paired (s : Index.{u} n) :
    firstConsecutive (SSet.S.mk s.paired.val) := by
  change (s.paired.val (0 : Fin (s.dim + 2))).val + 1 =
    (s.paired.val (1 : Fin (s.dim + 2))).val
  rw [Index.paired_zero]
  have hface := s.paired_faceIndex
  change s.paired.val (1 : Fin (s.dim + 2)) = s.pivot at hface
  rw [hface]
  rfl

private lemma not_firstConsecutive_simplex (s : Index.{u} n) :
    ¬ firstConsecutive (SSet.S.mk s.simplex) := by
  rcases s with ⟨_ | d, simplex, nonDegenerate, notMem, dim_pos, gap⟩
  · omega
  · change ¬ ((simplex (0 : Fin (d + 2))).val + 1 =
      (simplex (1 : Fin (d + 2))).val)
    have gap' : (simplex (0 : Fin (d + 2))).val + 1 <
        (simplex (1 : Fin (d + 2))).val := by
      simpa using gap
    omega

private lemma Index.injective_paired :
    Function.Injective (fun s : Index.{u} n => SSet.S.mk s.paired.val) := by
  intro s t h
  apply Index.ext
  simpa using congrArg unpair h

private lemma Index.injective_face : Function.Injective
    (fun s : Index.{u} n => SSet.S.mk
      ((Δ[n] : SSet.{u}).δ s.faceIndex s.paired.val)) := by
  intro s t h
  apply Index.ext
  simpa only [Index.paired_δ] using h

private lemma Index.paired_ne_simplex (s t : Index.{u} n) :
    SSet.S.mk s.paired.val ≠ SSet.S.mk t.simplex := by
  intro h
  have hs := firstConsecutive_paired s
  have ht := not_firstConsecutive_simplex t
  exact ht (h ▸ hs)

private lemma exists_index (hn : 2 ≤ n) (x : (spineSubcomplex.{u} n).N) :
    ∃ s : Index.{u} n,
      x.toS = SSet.S.mk s.paired.val ∨
        x.toS = SSet.S.mk
          ((Δ[n] : SSet.{u}).δ s.faceIndex s.paired.val) := by
  obtain ⟨d, simplex, nonDegenerate, notMem, rfl⟩ := x.mk_surjective
  have hd : 0 < d := outside_dim_pos n (by omega)
    (Subcomplex.N.mk simplex nonDegenerate notMem)
  by_cases hgap : (simplex (0 : Fin (d + 1))).val + 1 <
      (simplex (⟨1, Nat.succ_lt_succ hd⟩ : Fin (d + 1))).val
  · let s : Index.{u} n :=
      { dim := d
        simplex := simplex
        nonDegenerate := nonDegenerate
        notMem := notMem
        dim_pos := hd
        gap := hgap }
    refine ⟨s, Or.inr ?_⟩
    rw [Index.paired_δ]
    rfl
  · have hsmono : StrictMono simplex :=
      (stdSimplex.mem_nonDegenerate_iff_strictMono _).1 nonDegenerate
    have hlt := hsmono (show (0 : Fin (d + 1)) <
      (⟨1, Nat.succ_lt_succ hd⟩ : Fin (d + 1)) by
        exact Fin.mk_lt_mk.mpr Nat.zero_lt_one)
    have hconsecutive : (simplex (0 : Fin (d + 1))).val + 1 =
        (simplex (⟨1, Nat.succ_lt_succ hd⟩ : Fin (d + 1))).val := by
      omega
    have hd₂ : 2 ≤ d := by
      by_contra h
      have hd1 : d = 1 := by omega
      apply notMem
      subst d
      apply edge_mem_of_consecutive n simplex
      simpa using hconsecutive
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := by
      exact ⟨d - 1, by omega⟩
    have hk : 0 < k := by omega
    let face : (Δ[n] : SSet.{u}) _⦋k⦌ :=
      (Δ[n] : SSet.{u}).δ (1 : Fin (k + 2)) simplex
    have faceND : face ∈ (Δ[n] : SSet.{u}).nonDegenerate k := by
      exact nonDegenerate_δ nonDegenerate (1 : Fin (k + 2))
    have faceGap : (face (0 : Fin (k + 1))).val + 1 <
        (face (⟨1, Nat.succ_lt_succ hk⟩ : Fin (k + 1))).val := by
      dsimp [face]
      simp only [stdSimplex.δ_apply]
      have h12 := hsmono (show
        (⟨1, by omega⟩ : Fin (k + 2)) <
          (⟨2, by omega⟩ : Fin (k + 2)) by
            exact Fin.mk_lt_mk.mpr Nat.one_lt_two)
      have hc : (simplex (0 : Fin (k + 2))).val + 1 =
          (simplex (1 : Fin (k + 2))).val := by
        simpa using hconsecutive
      have hf0 : simplex ((1 : Fin (k + 2)).succAbove (0 : Fin (k + 1))) =
          simplex (0 : Fin (k + 2)) := by rfl
      have hf1 : simplex ((1 : Fin (k + 2)).succAbove
          (⟨1, Nat.succ_lt_succ hk⟩ : Fin (k + 1))) =
          simplex (⟨2, by omega⟩ : Fin (k + 2)) := by
        rw [Fin.succAbove_of_le_castSucc]
        · congr 1
        · exact le_rfl
      rw [hf0, hf1]
      omega
    have faceNot : face ∉ (spineSubcomplex.{u} n).obj (op ⦋k⦌) :=
      not_mem_of_gap n hk face faceND faceGap
    let s : Index.{u} n :=
      { dim := k
        simplex := face
        nonDegenerate := faceND
        notMem := faceNot
        dim_pos := hk
        gap := faceGap }
    have hp : s.paired.val = simplex := by
      apply stdSimplex.objEquiv.injective
      ext j
      change (s.paired.val j).val = (simplex j).val
      rw [Index.paired_apply]
      change ((Fin.insertNth (α := fun _ => Fin (n + 1))
        s.faceIndex s.pivot s.simplex) j).val = (simplex j).val
      have hi := Fin.insertNth_self_removeNth
        (p := (1 : Fin (k + 2))) simplex
      have hpivot : s.pivot = simplex (1 : Fin (k + 2)) := by
        apply Fin.ext
        dsimp [s, Index.pivot, face]
        have hc : (simplex (0 : Fin (k + 2))).val + 1 =
            (simplex (1 : Fin (k + 2))).val := by
          simpa using hconsecutive
        exact hc
      rw [show s.faceIndex = (1 : Fin (k + 2)) by rfl, hpivot]
      exact congrArg Fin.val (congrFun hi j)
    refine ⟨s, Or.inl ?_⟩
    rw [SSet.S.ext_iff]
    exact hp.symm

private noncomputable def pairingCore (n : ℕ) (hn : 2 ≤ n) :
    (spineSubcomplex.{u} n).PairingCore where
  ι := Index.{u} n
  dim s := s.dim
  simplex s := s.paired.val
  index s := s.faceIndex
  nonDegenerate₁ s := s.paired.property
  nonDegenerate₂ s := by
    rw [Index.paired_δ]
    exact s.nonDegenerate
  notMem₁ s := not_mem_of_two_le_dim (n := n) (d := s.dim + 1)
    (by have := s.dim_pos; omega) s.paired.val s.paired.property
  notMem₂ s := by
    rw [Index.paired_δ]
    exact s.notMem
  injective_type₁' h := Index.injective_paired h
  injective_type₂' h := Index.injective_face h
  type₁_ne_type₂' s t h := by
    apply Index.paired_ne_simplex s t
    simpa only [Index.paired_δ] using h
  surjective' x := exists_index (n := n) hn x

@[simp]
private lemma pairingCore_type₁ (n : ℕ) (hn : 2 ≤ n) (s : Index.{u} n) :
    (pairingCore.{u} n hn).type₁ s =
      Subcomplex.N.mk s.paired.val s.paired.property
        (not_mem_of_two_le_dim (n := n) (d := s.dim + 1)
          (by have := s.dim_pos; omega) s.paired.val s.paired.property) := by
  rfl

@[simp]
private lemma pairingCore_type₂ (n : ℕ) (hn : 2 ≤ n) (s : Index.{u} n) :
    (pairingCore.{u} n hn).type₂ s = s.toN := by
  rw [Subcomplex.N.eq_iff_sMk_eq]
  simp [Subcomplex.PairingCore.type₂, Index.toN, pairingCore]

private instance (n : ℕ) (hn : 2 ≤ n) : (pairingCore.{u} n hn).IsInner where
  ne_zero s h := by
    have hval := congrArg Fin.val h
    simp [pairingCore, Index.faceIndex, Index.i] at hval
  ne_last s h := by
    have hval := congrArg Fin.val h
    simp [pairingCore, Index.faceIndex, Index.i] at hval
    have := s.dim_pos
    omega

private def Index.span (s : Index.{u} n) : ℕ :=
  (s.simplex (Fin.last s.dim)).val -
    (s.simplex (0 : Fin (s.dim + 1))).val

private noncomputable def weakRankFunction (n : ℕ) (hn : 2 ≤ n) :
    (pairingCore.{u} n hn).WeakRankFunction ℕ where
  rank s := s.span
  lt := by
    intro s t hrel hdim
    change Index.{u} n at s t
    rcases s with ⟨sd, ss, snd, snm, sp, sg⟩
    rcases t with ⟨td, ts, tnd, tnm, tp, tg⟩
    change sd = td at hdim
    subst td
    let s : Index.{u} n := ⟨sd, ss, snd, snm, sp, sg⟩
    let t : Index.{u} n := ⟨sd, ts, tnd, tnm, tp, tg⟩
    change (pairingCore.{u} n hn).AncestralRel s t at hrel
    change s.span < t.span
    have hlt : s.toN <
        Subcomplex.N.mk t.paired.val t.paired.property
          (not_mem_of_two_le_dim (n := n) (d := t.dim + 1)
            (by have := t.dim_pos; omega) t.paired.val t.paired.property) := by
      have hlt := hrel.2
      rw [pairingCore_type₂, pairingCore_type₁] at hlt
      exact hlt
    obtain ⟨f, hf, hface⟩ := SSet.N.le_iff_exists_mono.1 hlt.le
    change ⦋sd⦌ ⟶ ⦋sd + 1⦌ at f
    let : Mono f := hf
    obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    change (Δ[n] : SSet.{u}).δ i t.paired.val = s.simplex at hface
    obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
    · have h0 := congrArg
        (fun z : (Δ[n] : SSet.{u}) _⦋sd⦌ => z (0 : Fin (sd + 1))) hface
      have hlast := congrArg
        (fun z : (Δ[n] : SSet.{u}) _⦋sd⦌ => z (Fin.last sd)) hface
      change t.paired.val ((0 : Fin (sd + 2)).succAbove 0) =
        s.simplex 0 at h0
      change t.paired.val ((0 : Fin (sd + 2)).succAbove (Fin.last sd)) =
        s.simplex (Fin.last sd) at hlast
      rw [Fin.succAbove_zero] at h0 hlast
      have h0' : t.pivot = s.simplex (0 : Fin (sd + 1)) := by
        have he : t.embedding (1 : Fin (sd + 2)) = t.pivot := by
          simpa [Index.faceIndex, Index.i] using t.embedding_faceIndex
        exact he.symm.trans h0
      have hlast' : t.simplex (Fin.last sd) =
          s.simplex (Fin.last sd) := by
        have he : t.embedding (Fin.last (sd + 1)) =
            t.simplex (Fin.last sd) := t.embedding_last
        exact he.symm.trans (by simpa [Fin.succ_last] using hlast)
      have htmono : StrictMono t.simplex :=
        (stdSimplex.mem_nonDegenerate_iff_strictMono _).1 t.nonDegenerate
      have hle := htmono.monotone (show t.one ≤ Fin.last sd from Fin.le_last _)
      change (t.simplex t.one).val ≤ (t.simplex (Fin.last sd)).val at hle
      have ht0pivot : (t.simplex (0 : Fin (sd + 1))).val < t.pivot.val := by
        simp [Index.pivot]
      have ht0last : (t.simplex (0 : Fin (sd + 1))).val <
          (t.simplex (Fin.last sd)).val := by
        have hg : t.pivot.val < (t.simplex t.one).val := by
          simpa [Index.pivot, Index.one] using t.gap
        exact lt_of_lt_of_le (lt_trans ht0pivot hg) hle
      have hsub := Nat.sub_lt_sub_left ht0last ht0pivot
      dsimp [Index.span]
      rw [← congrArg Fin.val h0', ← congrArg Fin.val hlast']
      exact hsub
    · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
      · have ht : (Δ[n] : SSet.{u}).δ (Fin.succ 0) t.paired.val =
            t.simplex := by
          simpa [Index.faceIndex, Index.i] using t.paired_δ
        have hst : s.simplex = t.simplex := hface.symm.trans ht
        exact (hrel.1 (Index.ext (n := n) ((SSet.S.ext_iff _ _).2 hst))).elim
      · have h0 := congrArg
          (fun z : (Δ[n] : SSet.{u}) _⦋sd⦌ => z (0 : Fin (sd + 1))) hface
        have h1 := congrArg
          (fun z : (Δ[n] : SSet.{u}) _⦋sd⦌ =>
            z s.one) hface
        change t.paired.val (j.succ.succ.succAbove 0) = s.simplex 0 at h0
        change t.paired.val (j.succ.succ.succAbove s.one) =
          s.simplex s.one at h1
        have hj0 : (0 : Fin (sd + 1)).castSucc < j.succ.succ := by
          apply Fin.mk_lt_mk.mpr
          simp
        have hj1 : s.one.castSucc < j.succ.succ := by
          apply Fin.mk_lt_mk.mpr
          simp [Index.one]
        rw [Fin.succAbove_of_castSucc_lt _ _ hj0] at h0
        rw [Fin.succAbove_of_castSucc_lt _ _ hj1] at h1
        have h0' : t.simplex (0 : Fin (sd + 1)) =
            s.simplex (0 : Fin (sd + 1)) := by
          exact t.embedding_zero.symm.trans h0
        have h1' : t.pivot = s.simplex s.one := by
          have hi : s.one.castSucc = t.faceIndex := by
            apply Fin.ext
            rfl
          rw [hi] at h1
          exact t.embedding_faceIndex.symm.trans h1
        have h0v := congrArg Fin.val h0'
        have h1v := congrArg Fin.val h1'
        have sg' : (s.simplex (0 : Fin (sd + 1))).val + 1 <
            (s.simplex s.one).val := by
          change (s.simplex (0 : Fin (sd + 1))).val + 1 <
            (s.simplex (⟨1, by omega⟩ : Fin (sd + 1))).val
          simpa using s.gap
        dsimp [Index.pivot] at h1v
        omega

private instance (n : ℕ) (hn : 2 ≤ n) : (pairingCore.{u} n hn).IsRegular :=
  (weakRankFunction.{u} n hn).isRegular

end spinePairing

/-- The inclusion of the consecutive-edge spine in the standard `n`-simplex
is inner anodyne when `2 ≤ n`. -/
theorem innerAnodyneExtensions_spineSubcomplex_ι (n : ℕ) (hn : 2 ≤ n) :
    innerAnodyneExtensions (spineSubcomplex.{u} n).ι :=
  (spinePairing.pairingCore.{u} n hn).pairing.innerAnodyneExtensions

/-- The consecutive-edge spine inclusion is a monic Joyal categorical
equivalence when `2 ≤ n`. -/
theorem monomorphisms_inf_categoricalEquivalences_spineSubcomplex_ι
    (n : ℕ) (hn : 2 ≤ n) :
    (MorphismProperty.monomorphisms SSet.{u} ⊓ categoricalEquivalences)
      (spineSubcomplex.{u} n).ι :=
  ⟨inferInstance, categoricalEquivalences.of_innerAnodyneExtensions
    (innerAnodyneExtensions_spineSubcomplex_ι n hn)⟩

end SSet.Rezk
