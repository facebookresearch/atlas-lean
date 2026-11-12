/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicDirichletComparison
import Mathlib.Combinatorics.SimpleGraph.Dart










namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section


def isingFiniteGraphDartSum
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (F : V → V → Real) : Real := by
  classical
  exact ∑ d : G.Dart, F d.fst d.snd

private def isingFiniteGraphDartEquiv
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (Σ x, G.neighborSet x) ≃ G.Dart where
  toFun p := ⟨(p.1, p.2.1), p.2.2⟩
  invFun d := ⟨d.fst, ⟨d.snd, d.adj⟩⟩
  left_inv p := by cases p; rfl
  right_inv d := by cases d; rfl



theorem isingFiniteGraphDartSum_eq_sum_laplacian
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (w u : V → Real) :
    isingFiniteGraphDartSum G (fun x y ↦ w x * (u y - u x)) =
      ∑ x, w x * isingFiniteGraphLaplacian G u x := by
  classical
  unfold isingFiniteGraphDartSum isingFiniteGraphLaplacian
  rw [← (isingFiniteGraphDartEquiv G).sum_comp
    (fun d : G.Dart ↦ w d.fst * (u d.snd - u d.fst))]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  let ex : G.neighborSet x ≃ {y // y ∈ G.neighborFinset x} :=
    { toFun := fun y ↦ ⟨y.1,
        (SimpleGraph.mem_neighborFinset G x y.1).2 y.2⟩
      invFun := fun y ↦ ⟨y.1,
        (SimpleGraph.mem_neighborFinset G x y.1).1 y.2⟩
      left_inv := fun y ↦ by ext; rfl
      right_inv := fun y ↦ by ext; rfl }
  calc
    (∑ y : G.neighborSet x, w x * (u y - u x)) =
        ∑ y : {y // y ∈ G.neighborFinset x},
          w x * (u y - u x) := by
            apply Fintype.sum_equiv ex
            intro y
            rfl
    _ = ∑ y ∈ G.neighborFinset x, w x * (u y - u x) := by
      simpa using Finset.sum_attach (G.neighborFinset x)
        (fun y ↦ w x * (u y - u x))


theorem isingFiniteGraphDartSum_swap
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (F : V → V → Real) :
    isingFiniteGraphDartSum G (fun x y ↦ F y x) =
      isingFiniteGraphDartSum G F := by
  classical
  let swap : G.Dart ≃ G.Dart :=
    { toFun := SimpleGraph.Dart.symm
      invFun := SimpleGraph.Dart.symm
      left_inv := SimpleGraph.Dart.symm_symm
      right_inv := SimpleGraph.Dart.symm_symm }
  have hsum := swap.sum_comp (fun d : G.Dart ↦ F d.fst d.snd)
  simpa [isingFiniteGraphDartSum, swap] using hsum


theorem isingFiniteGraphDartSum_cutoff_integrationByParts
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (eta u : V → Real) :
    2 * isingFiniteGraphDartSum G
        (fun x y ↦ eta x ^ 2 * u x * (u y - u x)) =
      -isingFiniteGraphDartSum G
          (fun x y ↦
            (eta y ^ 2 * u y - eta x ^ 2 * u x) * (u y - u x)) := by
  have hswap := isingFiniteGraphDartSum_swap G
    (fun x y ↦ eta x ^ 2 * u x * (u y - u x))
  calc
    2 * isingFiniteGraphDartSum G
        (fun x y ↦ eta x ^ 2 * u x * (u y - u x)) =
      isingFiniteGraphDartSum G
          (fun x y ↦ eta x ^ 2 * u x * (u y - u x)) +
        isingFiniteGraphDartSum G
          (fun x y ↦ eta y ^ 2 * u y * (u x - u y)) := by
            rw [hswap]
            ring
    _ = _ := by
      unfold isingFiniteGraphDartSum
      rw [← Finset.sum_add_distrib]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring




theorem isingFiniteGraph_caccioppoli_of_weighted_subharmonic
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (eta u : V → Real) (M : Real)
    (hu0 : ∀ x, 0 ≤ u x) (huM : ∀ x, u x ≤ M)
    (hweighted : 0 ≤ isingFiniteGraphDartSum G
      (fun x y ↦ eta x ^ 2 * u x * (u y - u x))) :
    isingFiniteGraphDartSum G
        (fun x y ↦ (eta y * u y - eta x * u x) ^ 2) ≤
      M ^ 2 * isingFiniteGraphDartSum G
        (fun x y ↦ (eta y - eta x) ^ 2) := by
  have hibp := isingFiniteGraphDartSum_cutoff_integrationByParts G eta u
  have halgebra :
      isingFiniteGraphDartSum G
          (fun x y ↦
            (eta y ^ 2 * u y - eta x ^ 2 * u x) * (u y - u x)) =
        isingFiniteGraphDartSum G
            (fun x y ↦ (eta y * u y - eta x * u x) ^ 2) -
          isingFiniteGraphDartSum G
            (fun x y ↦ u x * u y * (eta y - eta x) ^ 2) := by
    unfold isingFiniteGraphDartSum
    rw [← Finset.sum_sub_distrib]
    apply congrArg
    funext d
    ring
  have henergy : isingFiniteGraphDartSum G
      (fun x y ↦ (eta y * u y - eta x * u x) ^ 2) ≤
      isingFiniteGraphDartSum G
        (fun x y ↦ u x * u y * (eta y - eta x) ^ 2) := by
    rw [halgebra] at hibp
    linarith
  refine henergy.trans ?_
  unfold isingFiniteGraphDartSum
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro d hd
  have hM0 : 0 ≤ M := (hu0 d.fst).trans (huM d.fst)
  have hxy : u d.fst * u d.snd ≤ M ^ 2 := by
    nlinarith [hu0 d.fst, hu0 d.snd, huM d.fst, huM d.snd,
      mul_nonneg (sub_nonneg.mpr (huM d.fst))
        (sub_nonneg.mpr (huM d.snd))]
  exact mul_le_mul_of_nonneg_right hxy (sq_nonneg _)



theorem isingFiniteGraph_caccioppoli_of_subharmonicOn
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (boundary : V → Prop) (eta u : V → Real) (lower upper : Real)
    (hsub : IsingFiniteGraphSubharmonicOn G boundary u)
    (hlower : ∀ x, lower ≤ u x) (hupper : ∀ x, u x ≤ upper)
    (hsupport : ∀ x, eta x ≠ 0 → ¬ boundary x) :
    isingFiniteGraphDartSum G
        (fun x y ↦
          (eta y * (u y - lower) - eta x * (u x - lower)) ^ 2) ≤
      (upper - lower) ^ 2 *
        isingFiniteGraphDartSum G
          (fun x y ↦ (eta y - eta x) ^ 2) := by
  apply isingFiniteGraph_caccioppoli_of_weighted_subharmonic G eta
    (fun x ↦ u x - lower) (upper - lower)
  · intro x
    linarith [hlower x]
  · intro x
    linarith [hupper x]
  · rw [isingFiniteGraphDartSum_eq_sum_laplacian]
    apply Finset.sum_nonneg
    intro x hx
    by_cases heta : eta x = 0
    · simp [heta]
    · have hlap : 0 ≤ isingFiniteGraphLaplacian G u x :=
        hsub x (hsupport x heta)
      have hshift : isingFiniteGraphLaplacian G (fun y ↦ u y - lower) x =
          isingFiniteGraphLaplacian G u x := by
        simpa only [sub_eq_add_neg] using
          isingFiniteGraphLaplacian_add_const G u (-lower) x
      rw [hshift]
      exact mul_nonneg
        (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (hlower x))) hlap



theorem isingFiniteGraph_caccioppoli_of_superharmonicOn
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (boundary : V → Prop) (eta u : V → Real) (lower upper : Real)
    (hsuper : IsingFiniteGraphSuperharmonicOn G boundary u)
    (hlower : ∀ x, lower ≤ u x) (hupper : ∀ x, u x ≤ upper)
    (hsupport : ∀ x, eta x ≠ 0 → ¬ boundary x) :
    isingFiniteGraphDartSum G
        (fun x y ↦
          (eta y * (upper - u y) - eta x * (upper - u x)) ^ 2) ≤
      (upper - lower) ^ 2 *
        isingFiniteGraphDartSum G
          (fun x y ↦ (eta y - eta x) ^ 2) := by
  have hneg : IsingFiniteGraphSubharmonicOn G boundary (fun x ↦ -u x) := by
    intro x hx
    have hu := hsuper x hx
    rw [show (fun y ↦ -u y) = fun y ↦ (-1) * u y by
      funext y; ring,
      isingFiniteGraphLaplacian_const_mul] at ⊢
    linarith
  have h := isingFiniteGraph_caccioppoli_of_subharmonicOn G boundary eta
    (fun x ↦ -u x) (-upper) (-lower) hneg
    (fun x ↦ by linarith [hupper x])
    (fun x ↦ by linarith [hlower x]) hsupport
  simpa [sub_eq_add_neg, add_comm] using h




theorem isingFiniteGraph_compactVariation_sq_le_of_subharmonicOn
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (boundary : V → Prop) (eta u : V → Real) (lower upper c E : Real)
    (S : Finset G.Dart)
    (hsub : IsingFiniteGraphSubharmonicOn G boundary u)
    (hlower : ∀ x, lower ≤ u x) (hupper : ∀ x, u x ≤ upper)
    (hsupport : ∀ x, eta x ≠ 0 → ¬ boundary x)
    (hc : 0 ≤ c) (heta : ∀ d ∈ S, c ≤ eta d.snd)
    (hcutoff : isingFiniteGraphDartSum G
      (fun x y ↦ (eta y - eta x) ^ 2) ≤ E) :
    c ^ 2 *
        (∑ d ∈ S, |u d.snd - u d.fst|) ^ 2 ≤
      4 * (#S : Real) * (upper - lower) ^ 2 * E := by
  classical
  let v : V → Real := fun x ↦ u x - lower
  let M : Real := upper - lower
  have hv0 (x : V) : 0 ≤ v x := by
    dsimp [v]
    linarith [hlower x]
  have hvM (x : V) : v x ≤ M := by
    dsimp [v, M]
    linarith [hupper x]
  have hcacc := isingFiniteGraph_caccioppoli_of_subharmonicOn
    G boundary eta u lower upper hsub hlower hupper hsupport
  have hpoint (d : G.Dart) (hd : d ∈ S) :
      c ^ 2 * (v d.snd - v d.fst) ^ 2 ≤
        2 * (eta d.snd * v d.snd - eta d.fst * v d.fst) ^ 2 +
          2 * M ^ 2 * (eta d.snd - eta d.fst) ^ 2 := by
    have hetaD := heta d hd
    have heta0 : 0 ≤ eta d.snd := hc.trans hetaD
    have hcsq : c ^ 2 ≤ eta d.snd ^ 2 := by nlinarith
    have hvSq : v d.fst ^ 2 ≤ M ^ 2 := by
      nlinarith [hv0 d.fst, hvM d.fst]
    have hsplit :
        (eta d.snd * (v d.snd - v d.fst)) ^ 2 ≤
          2 * (eta d.snd * v d.snd - eta d.fst * v d.fst) ^ 2 +
            2 * (v d.fst * (eta d.fst - eta d.snd)) ^ 2 := by
      nlinarith [sq_nonneg
        ((eta d.snd * v d.snd - eta d.fst * v d.fst) -
          v d.fst * (eta d.fst - eta d.snd))]
    have htail :
        (v d.fst * (eta d.fst - eta d.snd)) ^ 2 ≤
          M ^ 2 * (eta d.snd - eta d.fst) ^ 2 := by
      have hs := sq_nonneg (eta d.snd - eta d.fst)
      nlinarith
    have hlowerSq :
        c ^ 2 * (v d.snd - v d.fst) ^ 2 ≤
          (eta d.snd * (v d.snd - v d.fst)) ^ 2 := by
      simpa only [mul_pow] using
        mul_le_mul_of_nonneg_right hcsq (sq_nonneg (v d.snd - v d.fst))
    calc
      _ ≤ _ := hlowerSq
      _ ≤ _ := hsplit
      _ ≤ _ := by nlinarith
  have henergy : c ^ 2 *
      (∑ d ∈ S, (v d.snd - v d.fst) ^ 2) ≤
        4 * M ^ 2 * E := by
    rw [Finset.mul_sum]
    calc
      (∑ d ∈ S, c ^ 2 * (v d.snd - v d.fst) ^ 2) ≤
          ∑ d ∈ S,
            (2 * (eta d.snd * v d.snd - eta d.fst * v d.fst) ^ 2 +
              2 * M ^ 2 * (eta d.snd - eta d.fst) ^ 2) := by
                apply sum_le_sum
                intro d hd
                exact hpoint d hd
      _ ≤ 2 * isingFiniteGraphDartSum G
              (fun x y ↦ (eta y * v y - eta x * v x) ^ 2) +
            2 * M ^ 2 * isingFiniteGraphDartSum G
              (fun x y ↦ (eta y - eta x) ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (by norm_num)
          unfold isingFiniteGraphDartSum
          exact Finset.sum_le_univ_sum_of_nonneg
            (fun d ↦ sq_nonneg _)
        · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (sq_nonneg M))
          unfold isingFiniteGraphDartSum
          exact Finset.sum_le_univ_sum_of_nonneg
            (fun d ↦ sq_nonneg _)
      _ ≤ 2 * (M ^ 2 * isingFiniteGraphDartSum G
              (fun x y ↦ (eta y - eta x) ^ 2)) +
            2 * M ^ 2 * isingFiniteGraphDartSum G
              (fun x y ↦ (eta y - eta x) ^ 2) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hcacc (by norm_num)) le_rfl
      _ ≤ 4 * M ^ 2 * E := by
        have hcutoff' := mul_le_mul_of_nonneg_left hcutoff (sq_nonneg M)
        nlinarith
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := S) (f := fun d : G.Dart ↦ |u d.snd - u d.fst|)
  simp only [sq_abs] at hcs
  have hvsub (d : G.Dart) : v d.snd - v d.fst = u d.snd - u d.fst := by
    dsimp [v]
    ring
  simp_rw [hvsub] at henergy
  calc
    c ^ 2 * (∑ d ∈ S, |u d.snd - u d.fst|) ^ 2 ≤
        c ^ 2 * ((#S : Real) *
          ∑ d ∈ S, (u d.snd - u d.fst) ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg c)
    _ ≤ (#S : Real) * (4 * M ^ 2 * E) := by
      nlinarith [show 0 ≤ (#S : Real) by positivity]
    _ = _ := by dsimp [M]; ring


theorem isingFiniteGraph_compactVariation_sq_le_of_superharmonicOn
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (boundary : V → Prop) (eta u : V → Real) (lower upper c E : Real)
    (S : Finset G.Dart)
    (hsuper : IsingFiniteGraphSuperharmonicOn G boundary u)
    (hlower : ∀ x, lower ≤ u x) (hupper : ∀ x, u x ≤ upper)
    (hsupport : ∀ x, eta x ≠ 0 → ¬ boundary x)
    (hc : 0 ≤ c) (heta : ∀ d ∈ S, c ≤ eta d.snd)
    (hcutoff : isingFiniteGraphDartSum G
      (fun x y ↦ (eta y - eta x) ^ 2) ≤ E) :
    c ^ 2 *
        (∑ d ∈ S, |u d.snd - u d.fst|) ^ 2 ≤
      4 * (#S : Real) * (upper - lower) ^ 2 * E := by
  have hneg : IsingFiniteGraphSubharmonicOn G boundary (fun x ↦ -u x) := by
    intro x hx
    have hu := hsuper x hx
    rw [show (fun y ↦ -u y) = fun y ↦ (-1) * u y by
      funext y; ring,
      isingFiniteGraphLaplacian_const_mul] at ⊢
    linarith
  have h := isingFiniteGraph_compactVariation_sq_le_of_subharmonicOn
    G boundary eta (fun x ↦ -u x) (-upper) (-lower) c E S hneg
    (fun x ↦ by linarith [hupper x])
    (fun x ↦ by linarith [hlower x]) hsupport hc heta hcutoff
  simpa only [neg_sub_neg, abs_sub_comm] using h

end

end StatMech.Universality
