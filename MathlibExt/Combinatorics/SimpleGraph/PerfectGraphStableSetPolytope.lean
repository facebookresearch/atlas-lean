/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBody
import Mathlib.Analysis.Convex.Combination

/-!
# Perfection and stable set polytopes

A finite graph is perfect exactly when its stable set polytope equals its clique-constrained
polytope.

Source: D. E. Knuth, "The Sandwich Theorem", Electron. J. Combin. 1 (1994), #A1
(arXiv:math/9312214v1), Theorem 32.
-/

public section

namespace MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBodyWanted

open MathlibExt.Combinatorics.SimpleGraph.LovaszTheta
open MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted
open Finset _root_.SimpleGraph

private theorem clique_map_of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) {Q : Finset V} (hQ : G.IsClique (Q : Set V)) :
    H.IsClique (Q.map f.toEmbedding : Set W) :=
  hQ.finsetMap.mono f.toHom.map_le

-- An induced subgraph of a pullback has the same chromatic and clique numbers as its image.
private theorem perfect_comap {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} (hG : IsPerfect G) (f : W → V) : IsPerfect (G.comap f) := by
  intro s
  let g : s → V := fun x => f x
  let t := Set.range g
  let p : s → t := fun x => ⟨g x, x, rfl⟩
  let H := G.induce t
  change (H.comap p).chromaticNumber = ((H.comap p).cliqueNum : ℕ∞)
  have hp : Function.Surjective p := by
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  let q := Function.surjInv hp
  have hq := Function.rightInverse_surjInv hp
  let qGraph : H ↪g H.comap p :=
    { toFun := q
      inj' := hq.injective
      map_rel_iff' := by
        intro x y
        change H.Adj (p (q x)) (p (q y)) ↔ H.Adj x y
        rw [hq x, hq y] }
  obtain ⟨Q, hQ⟩ := H.exists_isNClique_cliqueNum
  have hclique : H.cliqueNum ≤ (H.comap p).cliqueNum := by
    simpa [hQ.card_eq] using (clique_map_of_embedding qGraph hQ.isClique).card_le_cliqueNum
  apply le_antisymm ?_ (H.comap p).cliqueNum_le_chromaticNumber
  calc
    (H.comap p).chromaticNumber ≤ H.chromaticNumber :=
      chromaticNumber_mono_of_hom (Hom.comap p H)
    _ = (H.cliqueNum : ℕ∞) := hG t
    _ ≤ _ := by exact_mod_cast hclique

private theorem mem_stab_of_nat_weights {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : IsPerfect G) (w : V → ℕ) {n : ℕ} (hn : 0 < n)
    (hw : ∀ Q : Finset V, G.IsClique (Q : Set V) → ∑ v ∈ Q, w v ≤ n) :
    (fun v => (w v : ℝ) / n) ∈ stab G := by
  classical
  let W := Σ v, Fin (w v)
  let H : SimpleGraph W := (Gᶜ.comap Sigma.fst)ᶜ
  -- In the complement, the copies of each vertex form an independent set.
  have hH : IsPerfect H :=
    (lovasz_weak_perfect_graph_general _).mp
      (perfect_comap ((lovasz_weak_perfect_graph_general G).mp hG) Sigma.fst)
  have adj_of_adj {x y : W} (h : G.Adj x.1 y.1) : H.Adj x y := by
    refine ⟨fun e => G.loopless.irrefl _ (e ▸ h), fun h' => h'.2 h⟩
  have adj_same {v : V} {i j : Fin (w v)} (h : i ≠ j) :
      H.Adj (⟨v, i⟩ : W) ⟨v, j⟩ := by
    refine ⟨?_, fun h' => h'.1 rfl⟩
    exact fun e => h (eq_of_heq (Sigma.mk.inj_iff.mp e).2)
  have hclique : H.cliqueNum ≤ n := by
    obtain ⟨Q, hQ⟩ := H.exists_isNClique_cliqueNum
    let P := Q.image Sigma.fst
    have hP : G.IsClique (P : Set V) := by
      intro a ha b hb hab
      obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hb
      have hxy := hQ.isClique hx hy (fun e => hab (congrArg Sigma.fst e))
      exact not_not.mp fun h => hxy.2 ⟨hab, h⟩
    have hsub : Q ⊆ P.sigma (fun v => (univ : Finset (Fin (w v)))) :=
      fun x hx => mem_sigma.mpr ⟨mem_image_of_mem _ hx, mem_univ _⟩
    calc
      H.cliqueNum = Q.card := hQ.card_eq.symm
      _ ≤ (P.sigma (fun v => (univ : Finset (Fin (w v))))).card := card_le_card hsub
      _ = ∑ v ∈ P, w v := by simp
      _ ≤ n := hw P hP
  have hc : H.Colorable n := by
    rw [← chromaticNumber_le_iff_colorable, ← chromaticNumber_congr H.induceUnivIso,
      hH Set.univ]
    exact_mod_cast (H.cliqueNum_induce_le Set.univ).trans hclique
  obtain ⟨C⟩ := hc
  let S (c : Fin n) : Finset V := univ.filter fun v => ∃ i : Fin (w v), C ⟨v, i⟩ = c
  have hS (c : Fin n) : G.IsIndepSet (S c : Set V) := by
    intro u hu v hv _ huv
    obtain ⟨i, hi⟩ := (mem_filter.mp hu).2
    obtain ⟨j, hj⟩ := (mem_filter.mp hv).2
    exact C.valid (adj_of_adj huv) (hi.trans hj.symm)
  have hcount (v : V) : ∑ c : Fin n, charVec (S c) v = w v := by
    let col (i : Fin (w v)) := C ⟨v, i⟩
    have hinj : Function.Injective col := by
      intro i j h
      exact not_not.mp fun hne => C.valid (adj_same hne) h
    have hmem (c : Fin n) : v ∈ S c ↔ c ∈ univ.image col := by simp [S, col]
    simp only [charVec, hmem, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, mul_one,
      card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  apply mem_convexHull_of_exists_fintype (fun _ : Fin n => (n : ℝ)⁻¹) (charVec ∘ S)
  · intro c
    positivity
  · simp [Nat.ne_of_gt hn]
  · exact fun c => ⟨S c, hS c, rfl⟩
  · ext v
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, ← mul_sum,
      hcount, div_eq_inv_mul]

private theorem qstab_subset_stab_of_perfect {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : IsPerfect G) : qstab G ⊆ stab G := by
  classical
  rintro x ⟨hx, hclique⟩
  have hfinite : {z | ∃ S : Finset V, G.IsIndepSet (S : Set V) ∧ z = charVec S}.Finite :=
    (Set.finite_range charVec).subset fun _ ⟨S, _, hS⟩ => ⟨S, hS.symm⟩
  have hclosed : IsClosed (stab G) := hfinite.isClosed_convexHull ℝ
  -- Rounding down preserves every clique inequality and approximates each coordinate.
  rw [← hclosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (ε⁻¹ : ℝ)
  have hnR : 0 < (n : ℝ) := (inv_pos.mpr hε).trans hn
  have hnN : 0 < n := by exact_mod_cast hnR
  let w (v : V) := ⌊(n : ℝ) * x v⌋₊
  have hw (v : V) : (w v : ℝ) ≤ (n : ℝ) * x v :=
    Nat.floor_le (mul_nonneg hnR.le (hx v))
  have hwQ (Q : Finset V) (hQ : G.IsClique (Q : Set V)) : ∑ v ∈ Q, w v ≤ n := by
    exact_mod_cast calc
      ∑ v ∈ Q, (w v : ℝ) ≤ ∑ v ∈ Q, (n : ℝ) * x v := sum_le_sum fun v _ => hw v
      _ = (n : ℝ) * ∑ v ∈ Q, x v := by rw [mul_sum]
      _ ≤ n := mul_le_of_le_one_right hnR.le (hclique Q hQ)
  refine ⟨_, mem_stab_of_nat_weights hG w hnN hwQ, (dist_pi_lt_iff hε).mpr fun v => ?_⟩
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ((div_le_iff₀ hnR).mpr (by
    simpa [mul_comm] using hw v)))]
  have hfloor : (n : ℝ) * x v < (w v : ℝ) + 1 := Nat.lt_floor_add_one _
  have hεn : 1 < ε * n := by simpa [mul_comm] using (inv_lt_iff_one_lt_mul₀ hε).mp hn
  have hlt : x v - ε < (w v : ℝ) / n := by
    apply (lt_div_iff₀ hnR).mpr
    linarith only [hfloor, hεn, show (x v - ε) * n = n * x v - ε * n by ring]
  linarith

-- A positive coefficient in the convex combination must saturate every maximum clique.
private theorem exists_stable_meets_max_cliques {V : Type*} {G : SimpleGraph V}
    (heq : stab G = qstab G) (T : Finset V) (hT : T.Nonempty) :
    ∃ S : Finset V, G.IsIndepSet (S : Set V) ∧
      ∀ Q : Finset T, (G.induce (T : Set V)).IsNClique
        (G.induce (T : Set V)).cliqueNum Q → ∃ v ∈ Q, (v : V) ∈ S := by
  classical
  let H := G.induce (T : Set V)
  let k := H.cliqueNum
  have : Nonempty T := let ⟨v, hv⟩ := hT; ⟨⟨v, hv⟩⟩
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero H.cliqueNum_ne_zero_of_finite)
  let x (v : V) : ℝ := if v ∈ T then (k : ℝ)⁻¹ else 0
  have sum_x (P : Finset V) :
      ∑ v ∈ P, x v = ((P.filter (· ∈ T)).card : ℝ) * (k : ℝ)⁻¹ := by
    rw [← sum_filter]
    simp
  have hx : x ∈ qstab G := by
    refine ⟨fun v => by dsimp [x]; split_ifs <;> positivity, fun P hP => ?_⟩
    let P' := P.subtype (· ∈ T)
    have hP' : H.IsClique (P' : Set T) := by
      intro u hu v hv huv
      exact hP (mem_subtype.mp hu) (mem_subtype.mp hv) (Subtype.coe_injective.ne huv)
    have hcard : (P.filter (· ∈ T)).card ≤ k := by
      rw [← subtype_map, card_map]
      exact hP'.card_le_cliqueNum
    rw [sum_x, ← div_eq_mul_inv]
    exact (div_le_one hk).mpr
      (Nat.cast_le.mpr hcard)
  rw [← heq] at hx
  obtain ⟨ι, _, w, z, hw, htotal, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hx
  choose S hS hzS using hz
  obtain ⟨i, -, hi⟩ : ∃ i ∈ (univ : Finset ι), 0 < w i :=
    (sum_pos_iff_of_nonneg fun j _ => hw j).mp (by rw [htotal]; exact zero_lt_one)
  refine ⟨S i, hS i, fun Q hQ => ?_⟩
  let f : H ↪g G := Embedding.induce (T : Set V)
  let P := Q.map f.toEmbedding
  have hP : G.IsClique (P : Set V) := clique_map_of_embedding f hQ.isClique
  have hPT : ∀ v ∈ P, v ∈ T := by
    intro v hv
    obtain ⟨u, _, rfl⟩ := mem_map.mp hv
    exact u.property
  have hsumP : ∑ v ∈ P, x v = 1 := by
    rw [sum_x, filter_true_of_mem hPT, card_map, hQ.card_eq, mul_inv_cancel₀ hk.ne']
  have heval : ∑ j, w j * ∑ v ∈ P, charVec (S j) v = 1 := by
    simp only [mul_sum]
    rw [sum_comm, ← hsumP]
    refine sum_congr rfl fun v _ => ?_
    have hv := congrFun hsum v
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hzS] using hv
  by_contra! hmiss
  have hzero : ∑ v ∈ P, charVec (S i) v = 0 := by
    apply sum_eq_zero
    intro v hv
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hv
    change charVec (S i) (u : V) = 0
    simp [charVec, hmiss u hu]
  have hle (j : ι) : ∑ v ∈ P, charVec (S j) v ≤ 1 := by
    have hgen : charVec (S j) ∈ stab G := subset_convexHull ℝ _ ⟨S j, hS j, rfl⟩
    rw [heq] at hgen
    exact hgen.2 P hP
  have hlt : ∑ j, w j * ∑ v ∈ P, charVec (S j) v < ∑ j, w j := by
    apply sum_lt_sum (fun j _ => mul_le_of_le_one_right (hw j) (hle j))
    exact ⟨i, mem_univ _, by simpa [hzero] using hi⟩
  rw [heval, htotal] at hlt
  exact (lt_irrefl _ hlt)

private theorem perfect_of_stab_eq_qstab {V : Type*} [Fintype V] {G : SimpleGraph V}
    (heq : stab G = qstab G) : IsPerfect G := by
  classical
  have colorable (T : Finset V) :
      (G.induce (T : Set V)).Colorable (G.induce (T : Set V)).cliqueNum := by
    refine T.strongInductionOn ?_
    intro T ih
    by_cases hT : T.Nonempty
    · let H := G.induce (T : Set V)
      obtain ⟨S, hS, hmeet⟩ := exists_stable_meets_max_cliques heq T hT
      let R := T \ S
      have hRT : R ⊂ T := by
        obtain ⟨Q, hQ⟩ := H.exists_isNClique_cliqueNum
        obtain ⟨v, _, hv⟩ := hmeet Q hQ
        exact Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, fun h =>
          (mem_sdiff.mp (h.symm ▸ v.property : (v : V) ∈ R)).2 hv⟩
      let H' := G.induce (R : Set V)
      let f : H' ↪g H := induceHomOfLE G (Finset.coe_subset.mpr hRT.le)
      have hlt : H'.cliqueNum < H.cliqueNum := by
        obtain ⟨Q, hQ⟩ := H'.exists_isNClique_cliqueNum
        have hclique := clique_map_of_embedding f hQ.isClique
        have hle := hclique.card_le_cliqueNum
        rw [card_map, hQ.card_eq] at hle
        refine lt_of_le_of_ne hle fun he => ?_
        obtain ⟨v, hv, hvS⟩ := hmeet _ ⟨hclique, by rw [card_map, hQ.card_eq, he]⟩
        obtain ⟨u, _, rfl⟩ := mem_map.mp hv
        exact (mem_sdiff.mp u.property).2 hvS
      obtain ⟨C⟩ := ih R hRT
      refine Colorable.mono hlt ⟨Coloring.mk (fun v => if hv : (v : V) ∈ S then 0 else
        (C ⟨v, mem_sdiff.mpr ⟨v.property, hv⟩⟩).succ) ?_⟩
      intro u v huv
      by_cases hu : (u : V) ∈ S <;> by_cases hv : (v : V) ∈ S
      · exact (hS hu hv (G.ne_of_adj huv) huv).elim
      · rw [dite_eq_left hu, dite_eq_right hv]
        exact (Fin.succ_ne_zero _).symm
      · rw [dite_eq_right hu, dite_eq_left hv]
        exact Fin.succ_ne_zero _
      · rw [dite_eq_right hu, dite_eq_right hv]
        intro he
        exact C.valid (v := ⟨u, mem_sdiff.mpr ⟨u.property, hu⟩⟩)
          (w := ⟨v, mem_sdiff.mpr ⟨v.property, hv⟩⟩) huv (Fin.succ_inj.mp he)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hT]
      have : IsEmpty (↥((∅ : Finset V) : Set V)) :=
        ⟨fun v => Finset.notMem_empty _ v.property⟩
      exact Colorable.of_isEmpty _
  intro t
  let T := t.toFinset
  have hT : (T : Set V) = t := t.coe_toFinset
  have hc : (G.induce t).Colorable (G.induce t).cliqueNum := hT ▸ colorable T
  exact le_antisymm hc.chromaticNumber_le cliqueNum_le_chromaticNumber

/-- **Perfect graphs are those with STAB = QSTAB.** A finite graph `G` is perfect if and only if
`STAB(G) = QSTAB(G)` (Knuth, *The Sandwich Theorem*, 1994, Theorem 32; the direction "perfect
implies equal" is his Theorem 31). -/
theorem isPerfect_iff_stab_eq_qstab {V : Type*} [Fintype V] (G : SimpleGraph V) :
    MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.IsPerfect G ↔ stab G = qstab G := by
  refine ⟨fun h => Set.Subset.antisymm ((stab_subset_th G).trans (th_subset_qstab G))
    (qstab_subset_stab_of_perfect h), perfect_of_stab_eq_qstab⟩

end MathlibExt.Combinatorics.SimpleGraph.LovaszThetaBodyWanted
