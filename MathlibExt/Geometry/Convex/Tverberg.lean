/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import MathlibExt.Geometry.Convex.ColorfulCaratheodory

@[expose] public section

section
namespace MathlibExt.Geometry.Convex.TverbergWanted

/--
**Tverberg's theorem.** Let $d, r$ be natural numbers with $r \ge 1$ and let $N = (d+1)(r-1)+1$.
For any points $p_1, \dots, p_N$ of $\mathbb{R}^d$, not necessarily distinct, there are pairwise
disjoint sets $P_1, \dots, P_r \subseteq \{1, \dots, N\}$ whose union is $\{1, \dots, N\}$ and a
point $x \in \mathbb{R}^d$ that lies in the convex hull of $\{p_i : i \in P_j\}$ for every $j$.

Proves `Wanted` entry `tverberg`.

Source: H. Tverberg, J. London Math. Soc. s1-41 (1966), 123-128, DOI 10.1112/jlms/s1-41.1.123.
-/
theorem tverberg
    {d r : ℕ} (hr : 0 < r)
    (pts : Fin ((d + 1) * (r - 1) + 1) → EuclideanSpace ℝ (Fin d)) :
    ∃ (P : Fin r → Set (Fin ((d + 1) * (r - 1) + 1)))
      (x : EuclideanSpace ℝ (Fin d)),
      (∀ i₁ i₂, i₁ ≠ i₂ → Disjoint (P i₁) (P i₂)) ∧
      (⋃ j, P j) = Set.univ ∧
      ∀ j, x ∈ convexHull ℝ (pts '' P j) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  set ef : Fin (n + 1) → EuclideanSpace ℝ (Fin n) :=
    fun j => WithLp.toLp (2 : ENNReal)
      (fun k : Fin n => if j.val < n then (if j.val = k.val then (1 : ℝ) else 0) else (-1 : ℝ)) with
          hef
  have hef_app : ∀ (j : Fin (n + 1)) (k : Fin n),
      ef j k = (if j.val < n then (if j.val = k.val then (1 : ℝ) else 0) else (-1 : ℝ)) := by
    intro j k
    rw [hef]
  set φ : Fin ((d + 1) * (n + 1 - 1) + 1) → EuclideanSpace ℝ (Fin (d + 1)) :=
    fun i => WithLp.toLp (2 : ENNReal)
      (fun kc : Fin (d + 1) => if hc : kc.val < d then pts i ⟨kc.val, hc⟩ else 1) with hφ
  have hφ_app : ∀ (i) (kc : Fin (d + 1)),
      φ i kc = (if hc : kc.val < d then pts i ⟨kc.val, hc⟩ else 1) := by
    intro i kc
    rw [hφ]
  set p : Fin ((d + 1) * (n + 1 - 1) + 1) → Fin (n + 1) →
      EuclideanSpace ℝ (Fin n × Fin (d + 1)) :=
    fun i j => WithLp.toLp (2 : ENNReal)
      (fun jk : Fin n × Fin (d + 1) => ef j jk.1 * φ i jk.2) with hp
  have hp_app : ∀ (i) (j : Fin (n + 1)) (jk : Fin n × Fin (d + 1)),
      p i j jk = ef j jk.1 * φ i jk.2 := by
    intro i j jk
    rw [hp]
  set S : Fin ((d + 1) * (n + 1 - 1) + 1) → Finset (EuclideanSpace ℝ (Fin n × Fin (d + 1))) :=
    fun l => Finset.univ.image (fun j : Fin (n + 1) => p l j) with hS
  have hlast2 : ∀ k' : Fin n, ef (Fin.last n) k' = -1 := by
    intro k'
    rw [hef_app, ite_eq_right (by rw [Fin.val_last]; exact lt_irrefl _)]
  have hsum_ef : ∀ k' : Fin n, ∑ j : Fin (n + 1), ef j k' = 0 := by
    intro k'
    rw [Fin.sum_univ_castSucc]
    change (∑ k'' : Fin n, ef (k''.castSucc) k') + ef (Fin.last n) k' = 0
    have ho1 : ef (k'.castSucc) k' = 1 := by
      rw [hef_app, ite_eq_left (by rw [Fin.val_castSucc]; exact k'.2),
        ite_eq_left (by rw [Fin.val_castSucc])]
    have hz1 : ∀ b : Fin n, b ≠ k' → ef (b.castSucc) k' = 0 := by
      intro b hb
      rw [hef_app, ite_eq_left (by rw [Fin.val_castSucc]; exact b.2)]
      apply ite_eq_right
      intro hcon
      apply hb
      apply Fin.ext
      rw [Fin.val_castSucc] at hcon
      exact hcon
    have hmid : (∑ k'' : Fin n, ef (k''.castSucc) k') = 1 :=
      calc (∑ k'' : Fin n, ef (k''.castSucc) k') = ef (k'.castSucc) k' :=
            Finset.sum_eq_single k'
              (fun b _ hb => by
                change ef (b.castSucc) k' = 0
                exact hz1 b hb)
              (fun h => absurd (Finset.mem_univ k') h)
        _ = 1 := ho1
    rw [hmid, hlast2 k']
    norm_num
  have sumapp : ∀ (ι κ : Type) (s : Finset ι) (f : ι → EuclideanSpace ℝ κ) (k : κ),
      ((∑ i ∈ s, f i)) k = ∑ i ∈ s, f i k := by
    intro ι κ s f k
    exact map_sum ({ toFun := fun v : EuclideanSpace ℝ κ => v k, map_zero' := rfl, map_add' := fun _
        _ => rfl } : EuclideanSpace ℝ κ →+ ℝ) f s
  have hpush : ∀ (κ : Type) (c : ℝ) (v : EuclideanSpace ℝ κ) (k : κ),
      (c • v) k = c * v k := by
    intro κ c v k
    exact rfl
  have hsum_p_vec : ∀ l, ∑ j : Fin (n + 1), p l j = 0 := by
    intro l
    apply PiLp.ext
    intro jk
    change ((∑ j : Fin (n + 1), p l j)) jk = ((0 : EuclideanSpace ℝ (Fin n × Fin (d + 1))) jk)
    rw [sumapp _ _ _ _ jk]
    show (∑ j : Fin (n + 1), p l j jk) = ((0 : EuclideanSpace ℝ (Fin n × Fin (d + 1))) jk)
    simp only [hp_app]
    rw [← Finset.sum_mul, hsum_ef, zero_mul, PiLp.zero_apply]
  have hnR : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (by omega))
  have hwr : (∑ _j : Fin (n + 1), (1 / ((n + 1 : ℕ) : ℝ))) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one_div_cancel hnR]
  have hcomb0 : ∀ l, (∑ j : Fin (n + 1), (1 / ((n + 1 : ℕ) : ℝ)) • p l j) = 0 := by
    intro l
    rw [← Finset.smul_sum, hsum_p_vec l, smul_zero]
  have hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin n × Fin (d + 1))) + 1
      = (d + 1) * (n + 1 - 1) + 1 := by
    rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Nat.add_sub_cancel, mul_comm]
  have h0 : ∀ l, (0 : EuclideanSpace ℝ (Fin n × Fin (d + 1))) ∈
      convexHull ℝ (↑(S l) : Set _) := by
    intro l
    rw [← hcomb0 l]
    apply (convex_convexHull ℝ _).sum_mem
    · intro j _
      exact div_nonneg one_pos.le (Nat.cast_nonneg _)
    · exact hwr
    · intro j _
      apply subset_convexHull ℝ _
      simp only [hS]
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  obtain ⟨t, ht⟩ :=
    MathlibExt.Geometry.Convex.ColorfulCaratheodoryWanted.colorful_caratheodory_finrank hm S h0
  obtain ⟨ι', hι', z, w, hrange, hAI, hpos, hsum, hrfl⟩ :=
    eq_pos_convex_span_of_mem_convexHull (𝕜 := ℝ) ht
  let := hι'
  have hex : ∀ l, ∃ j : Fin (n + 1), (t l : EuclideanSpace ℝ (Fin n × Fin (d + 1))) = p l j := by
    intro l
    have hmem : (t l : EuclideanSpace ℝ (Fin n × Fin (d + 1))) ∈ S l := (t l).2
    simp only [hS] at hmem
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
    exact ⟨j, hj.symm⟩
  choose li hli using hex
  have hex2 : ∀ i : ι', ∃ l, z i = (t l : EuclideanSpace ℝ (Fin n × Fin (d + 1))) := by
    intro i
    obtain ⟨l, hl⟩ := hrange (Set.mem_range_self i)
    exact ⟨l, hl.symm⟩
  choose lof hlo using hex2
  have hzi : ∀ i : ι', z i = p (lof i) (li (lof i)) := fun i => by rw [hlo i, hli (lof i)]
  set fib : Fin (n + 1) → Finset ι' :=
    fun j => Finset.univ.filter (fun i => li (lof i) = j) with hfib
  set F : Fin (n + 1) → Fin (d + 1) → ℝ :=
    fun j kc => ∑ i ∈ fib j, w i * φ (lof i) kc with hF
  set W : Fin (n + 1) → ℝ := fun j => ∑ i ∈ fib j, w i with hW
  have hfibmem : ∀ (j) (i), i ∈ fib j ↔ li (lof i) = j := by
    intro j i
    simp only [hfib, Finset.mem_filter, Finset.mem_univ, true_and]
  have hFapp : ∀ (j) (kc), F j kc = ∑ i ∈ fib j, w i * φ (lof i) kc := by
    intro j kc
    rw [hF]
  have hWapp : ∀ j, W j = ∑ i ∈ fib j, w i := by
    intro j
    rw [hW]
  have hφlast : ∀ i, φ i (Fin.last d) = 1 := by
    intro i
    rw [hφ_app, dite_eq_right (by rw [Fin.val_last]; exact lt_irrefl _)]
  have hφcs : ∀ (i) (kd : Fin d), φ i kd.castSucc = pts i kd := by
    intro i kd
    rw [hφ_app, dite_eq_left (by rw [Fin.val_castSucc]; exact kd.2)]
    apply congrArg (fun a => pts i a)
    apply Fin.ext
    rw [Fin.val_castSucc]
  have hcoor0 : ∀ (k' : Fin n) (kc : Fin (d + 1)),
      (∑ i, w i * (ef (li (lof i)) k' * φ (lof i) kc)) = 0 := by
    intro k' kc
    have hbase : ((∑ i, w i • z i)) (k', kc)
        = ((0 : EuclideanSpace ℝ (Fin n × Fin (d + 1)))) (k', kc) := by
      rw [hrfl]
    rw [sumapp _ _ _ _ (k', kc)] at hbase
    simp only [hpush, hzi, hp_app] at hbase
    exact hbase
  have hfib_lemma : ∀ (k' : Fin n) (kc : Fin (d + 1)) (j : Fin (n + 1)),
      ef j k' * F j kc = ∑ i ∈ fib j, w i * (ef (li (lof i)) k' * φ (lof i) kc) := by
    intro k' kc j
    rw [hFapp j kc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hji : li (lof i) = j := (hfibmem j i).mp hi
    rw [hji]
    ring
  have hcoor : ∀ (k' : Fin n) (kc : Fin (d + 1)), ∑ j : Fin (n + 1), ef j k' * F j kc = 0 := by
    intro k' kc
    calc (∑ j : Fin (n + 1), ef j k' * F j kc)
        = ∑ j : Fin (n + 1), ∑ i ∈ fib j, w i * (ef (li (lof i)) k' * φ (lof i) kc) :=
          Finset.sum_congr rfl (fun j _ => hfib_lemma k' kc j)
      _ = ∑ i, w i * (ef (li (lof i)) k' * φ (lof i) kc) := by
          simp only [hfib]
          exact Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ _) _
      _ = 0 := hcoor0 k' kc
  have efkey : ∀ (G : Fin (n + 1) → ℝ), (∀ k' : Fin n, ∑ j, ef j k' * G j = 0) →
      ∀ j, G j = G (Fin.last n) := by
    intro G hG j
    by_cases hj : j = Fin.last n
    · rw [hj]
    · have hjn : j.val < n := by
        by_contra hc
        push Not at hc
        have h2 : j.val = n := by
          have h1 := j.2
          omega
        apply hj
        apply Fin.ext
        rw [Fin.val_last]
        exact h2
      have hmain := hG ⟨j.val, hjn⟩
      rw [Fin.sum_univ_castSucc] at hmain
      change (∑ k'' : Fin n, ef (k''.castSucc) (⟨j.val, hjn⟩ : Fin n) * G (k''.castSucc))
        + ef (Fin.last n) (⟨j.val, hjn⟩ : Fin n) * G (Fin.last n) = 0 at hmain
      have ho : ef ((⟨j.val, hjn⟩ : Fin n).castSucc) (⟨j.val, hjn⟩ : Fin n) = 1 := by
        rw [hef_app, ite_eq_left (by rw [Fin.val_castSucc]; exact (⟨j.val, hjn⟩ : Fin n).2),
          ite_eq_left (by rw [Fin.val_castSucc])]
      have hll : ef (Fin.last n) (⟨j.val, hjn⟩ : Fin n) = -1 := hlast2 _
      have hsingle : (∑ k'' : Fin n, ef (k''.castSucc) (⟨j.val, hjn⟩ : Fin n) * G (k''.castSucc))
          = ef ((⟨j.val, hjn⟩ : Fin n).castSucc) (⟨j.val, hjn⟩ : Fin n) *
            G ((⟨j.val, hjn⟩ : Fin n).castSucc) :=
        Finset.sum_eq_single _
          (fun b _ hb => by
            change ef (b.castSucc) (⟨j.val, hjn⟩ : Fin n) * G (b.castSucc) = 0
            have hb0 : ef (b.castSucc) (⟨j.val, hjn⟩ : Fin n) = 0 := by
              rw [hef_app, ite_eq_left (by rw [Fin.val_castSucc]; exact b.2)]
              apply ite_eq_right
              intro hcon
              apply hb
              apply Fin.ext
              rw [Fin.val_castSucc] at hcon
              exact hcon
            rw [hb0, zero_mul])
          (fun h => absurd (Finset.mem_univ _) h)
      rw [hsingle, ho, hll] at hmain
      have hcast : (⟨j.val, hjn⟩ : Fin n).castSucc = j := Fin.ext rfl
      rw [hcast] at hmain
      have hcon : G j = G (Fin.last n) := by linear_combination hmain
      exact hcon
  have hFeq : ∀ (kc : Fin (d + 1)) (j : Fin (n + 1)), F j kc = F (Fin.last n) kc := by
    intro kc j
    exact efkey (fun j => F j kc) (fun k' => hcoor k' kc) j
  have hFW : ∀ j, F j (Fin.last d) = W j := by
    intro j
    rw [hFapp j (Fin.last d), hWapp j]
    simp only [hφlast, mul_one]
  have hWeq : ∀ j, W j = W (Fin.last n) := by
    intro j
    rw [← hFW j, ← hFW (Fin.last n)]
    exact hFeq _ j
  have hWtot : (∑ j : Fin (n + 1), W j) = 1 := by
    have e : (∑ j : Fin (n + 1), W j) = ∑ i, w i := by
      calc (∑ j : Fin (n + 1), W j) = ∑ j : Fin (n + 1), ∑ i ∈ fib j, w i :=
            Finset.sum_congr rfl (fun j _ => hWapp j)
        _ = ∑ i, w i := by
            simp only [hfib]
            exact Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ _) _
    rw [e]
    exact hsum
  have hWval : W (Fin.last n) = 1 / ((n + 1 : ℕ) : ℝ) := by
    have heq : (∑ j : Fin (n + 1), W j) = ((n + 1 : ℕ) : ℝ) * W (Fin.last n) := by
      calc (∑ j : Fin (n + 1), W j) = ∑ _j : Fin (n + 1), W (Fin.last n) :=
            Finset.sum_congr rfl (fun j _ => hWeq j)
        _ = ((n + 1 : ℕ) : ℝ) * W (Fin.last n) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hmul : ((n + 1 : ℕ) : ℝ) * W (Fin.last n) = 1 := by
      rw [← heq]
      exact hWtot
    rw [eq_div_iff hnR, mul_comm]
    exact hmul
  have hWpos : 0 < W (Fin.last n) := by
    rw [hWval]
    apply div_pos one_pos
    exact Nat.cast_pos.mpr (by omega)
  set x : EuclideanSpace ℝ (Fin d) :=
    WithLp.toLp (2 : ENNReal)
      (fun kd : Fin d => (W (Fin.last n))⁻¹ * F (Fin.last n) (kd.castSucc)) with hx
  have hx_app : ∀ kd : Fin d, x kd = (W (Fin.last n))⁻¹ * F (Fin.last n) (kd.castSucc) := by
    intro kd
    rw [hx]
  refine ⟨fun j => {l | li l = j}, x, ?_, ?_, ?_⟩
  · intro i₁ i₂ hne
    apply Set.disjoint_left.mpr
    intro l h1 h2
    have e1 : li l = i₁ := h1
    have e2 : li l = i₂ := h2
    exact hne (e1.symm.trans e2)
  · rw [Set.eq_univ_iff_forall]
    intro l
    exact Set.mem_iUnion.mpr ⟨li l, rfl⟩
  · intro j
    have hcombo : (∑ i ∈ fib j, ((W (Fin.last n))⁻¹ * w i) • pts (lof i)) = x := by
      apply PiLp.ext
      intro kd
      change ((∑ i ∈ fib j, ((W (Fin.last n))⁻¹ * w i) • pts (lof i))) kd = x kd
      rw [sumapp _ _ _ _ kd, hx_app]
      simp only [hpush]
      have e1 : (∑ i ∈ fib j, (W (Fin.last n))⁻¹ * w i * pts (lof i) kd)
          = (W (Fin.last n))⁻¹ * F j (kd.castSucc) := by
        rw [hFapp j (kd.castSucc), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hφcs (lof i) kd]
        ring
      rw [e1, hFeq _ j]
    rw [← hcombo]
    apply (convex_convexHull ℝ _).sum_mem
    · intro i _
      apply mul_nonneg (le_of_lt (inv_pos.mpr hWpos)) (le_of_lt (hpos i))
    · have e2 : (∑ i ∈ fib j, (W (Fin.last n))⁻¹ * w i) = (W (Fin.last n))⁻¹ * W j := by
        rw [hWapp j, Finset.mul_sum]
      rw [e2, hWeq j, inv_mul_cancel₀ (ne_of_gt hWpos)]
    · intro i hi
      apply subset_convexHull ℝ _
      exact ⟨lof i, (hfibmem j i).mp hi, rfl⟩

end MathlibExt.Geometry.Convex.TverbergWanted
