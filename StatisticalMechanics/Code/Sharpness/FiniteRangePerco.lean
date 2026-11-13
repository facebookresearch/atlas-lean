/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Probability.InhomogeneousProduct
import Code.Percolation.SubcriticalDecayFull
import Code.Percolation.SurfaceReassembly
import Code.Sharpness.BkCriterionFull

open MeasureTheory
open scoped NNReal

namespace StatMech
namespace Sharpness

open ConfigSpace Lattice Percolation



structure FiniteRangeKernel (d : ℕ) where
  coupling : Site d → ℝ
  nonneg : ∀ z, 0 ≤ coupling z
  zero : coupling 0 = 0
  symmetric : ∀ z, coupling (-z) = coupling z
  range : ℕ
  support : ∀ z, coupling z ≠ 0 → z ∈ box d range

variable {d : ℕ}


theorem frp_finset_subset_box (S : Finset (Site d)) :
    ∃ N : ℕ, (S : Set (Site d)) ⊆ box d N := by
  classical
  refine ⟨S.sup (fun x => Finset.univ.sup (fun i => (x i).natAbs)), ?_⟩
  intro x hx
  rw [Finset.mem_coe] at hx
  rw [mem_box]
  intro i
  calc
    (x i).natAbs ≤ Finset.univ.sup (fun j => (x j).natAbs) :=
      Finset.le_sup (f := fun j => (x j).natAbs) (Finset.mem_univ i)
    _ ≤ S.sup (fun y => Finset.univ.sup (fun j => (y j).natAbs)) :=
      Finset.le_sup (f := fun y => Finset.univ.sup (fun j => (y j).natAbs)) hx


noncomputable def frpEdgeCoupling (K : FiniteRangeKernel d) :
    Sym2 (Site d) → ℝ :=
  Sym2.lift ⟨fun x y => K.coupling (y - x), by
    intro x y
    dsimp only
    rw [show x - y = -(y - x) by abel, K.symmetric]⟩

@[simp] theorem frpEdgeCoupling_mk (K : FiniteRangeKernel d) (x y : Site d) :
    frpEdgeCoupling K s(x, y) = K.coupling (y - x) := rfl



noncomputable def frpGraph (K : FiniteRangeKernel d) : SimpleGraph (Site d) where
  Adj x y := 0 < K.coupling (y - x)
  symm := by
    intro x y h
    rwa [show x - y = -(y - x) by abel, K.symmetric]
  loopless := ⟨by
    intro x h
    have hz : x - x = (0 : Site d) := sub_self x
    rw [hz, K.zero] at h
    exact (lt_irrefl 0 h)⟩

noncomputable instance (K : FiniteRangeKernel d) : DecidableRel (frpGraph K).Adj :=
  Classical.decRel _


noncomputable def frpEdgeParam (K : FiniteRangeKernel d) (beta : ℝ)
    (e : Sym2 (Site d)) : ℝ≥0 :=
  Real.toNNReal (1 - Real.exp (-beta * frpEdgeCoupling K e))

theorem frpEdgeParam_le_one (K : FiniteRangeKernel d) (beta : ℝ) (e) :
    frpEdgeParam K beta e ≤ 1 := by
  unfold frpEdgeParam
  rw [Real.toNNReal_le_one]
  have hpos := Real.exp_pos (-beta * frpEdgeCoupling K e)
  linarith


noncomputable def frpMeasure (K : FiniteRangeKernel d) (beta : ℝ) :
    Measure (ConfigSpace (Sym2 (Site d))) :=
  inhomBernoulliProductMeasure (frpEdgeParam K beta)
    (frpEdgeParam_le_one K beta)

noncomputable instance (K : FiniteRangeKernel d) (beta : ℝ) :
    IsProbabilityMeasure (frpMeasure K beta) := by
  unfold frpMeasure
  infer_instance


theorem frpEdgeCoupling_smul (K : FiniteRangeKernel d)
    (g : Multiplicative (Site d)) (e : Sym2 (Site d)) :
    frpEdgeCoupling K (g • e) = frpEdgeCoupling K e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [smul_sym2_mk, frpEdgeCoupling_mk, frpEdgeCoupling_mk]
      congr 1
      funext i
      rw [Pi.sub_apply]
      simp only [smul_site_apply]
      simp only [Pi.sub_apply]
      abel


theorem frpEdgeParam_smul (K : FiniteRangeKernel d) (beta : ℝ)
    (g : Multiplicative (Site d)) (e : Sym2 (Site d)) :
    frpEdgeParam K beta (g • e) = frpEdgeParam K beta e := by
  unfold frpEdgeParam
  rw [frpEdgeCoupling_smul]



theorem frpMeasure_translationInvariant (K : FiniteRangeKernel d) (beta : ℝ) :
    IsTranslationInvariant (G := Multiplicative (Site d)) (frpMeasure K beta) := by
  intro g
  refine ⟨measurable_shift g, ?_⟩
  rw [shift_eq_piCongrLeft]
  let e := MulAction.toPerm (β := Sym2 (Site d)) g
  have h := Measure.infinitePi_map_piCongrLeft
    (μ := fun i : Sym2 (Site d) =>
      bernoulliMeasure (frpEdgeParam K beta i) (frpEdgeParam_le_one K beta i)) e
  change Measure.map
      (Equiv.piCongrLeft (fun _ : Sym2 (Site d) => Bool) e)
        (Measure.infinitePi (fun i =>
          bernoulliMeasure (frpEdgeParam K beta i) (frpEdgeParam_le_one K beta i))) = _
  rw [show (fun i =>
      bernoulliMeasure (frpEdgeParam K beta i) (frpEdgeParam_le_one K beta i)) =
      (fun i => bernoulliMeasure (frpEdgeParam K beta (e i))
        (frpEdgeParam_le_one K beta (e i))) from by
        funext i
        have hpi : frpEdgeParam K beta (e i) = frpEdgeParam K beta i := by
          simpa [e] using frpEdgeParam_smul K beta g i
        exact bernoulliMeasure_congr _ _ hpi.symm]
  exact h


theorem frpGraph_adj_displacement (K : FiniteRangeKernel d) {x y : Site d}
    (hxy : (frpGraph K).Adj x y) : y - x ∈ box d K.range :=
  K.support (y - x) (ne_of_gt hxy)


noncomputable def frpSteps (K : FiniteRangeKernel d) : Finset (Site d) :=
  (box_finite d K.range).toFinset.filter (fun z => 0 < K.coupling z)

theorem mem_frpSteps (K : FiniteRangeKernel d) {z : Site d} :
    z ∈ frpSteps K ↔ 0 < K.coupling z := by
  rw [frpSteps, Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨K.support z (ne_of_gt h), h⟩


noncomputable def frpBoundaryPairs (K : FiniteRangeKernel d)
    (S : Finset (Site d)) : Finset (Site d × Site d) :=
  ((S ×ˢ frpSteps K).image fun xz => (xz.1, xz.1 + xz.2)).filter
    (fun q => q.2 ∉ S)

theorem mem_frpBoundaryPairs (K : FiniteRangeKernel d) (S : Finset (Site d))
    {x y : Site d} :
    (x, y) ∈ frpBoundaryPairs K S ↔
      x ∈ S ∧ y ∉ S ∧ (frpGraph K).Adj x y := by
  classical
  rw [frpBoundaryPairs, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨a, z⟩, haz, hmap⟩, hyS⟩
    rw [Finset.mem_product] at haz
    simp only [Prod.mk.injEq] at hmap
    rcases hmap with ⟨rfl, rfl⟩
    refine ⟨haz.1, hyS, ?_⟩
    change 0 < K.coupling ((a + z) - a)
    rw [add_sub_cancel_left]
    exact (mem_frpSteps K).mp haz.2
  · rintro ⟨hxS, hyS, hxy⟩
    let z := y - x
    have hz : z ∈ frpSteps K := (mem_frpSteps K).mpr hxy
    have hsum : x + z = y := by simp [z]
    refine ⟨⟨(x, z), Finset.mem_product.mpr ⟨hxS, hz⟩, ?_⟩, hyS⟩
    simp [hsum]


noncomputable def frpInternalEdges (S : Finset (Site d)) :
    Finset (Sym2 (Site d)) :=
  (S ×ˢ S).image (fun xy => s(xy.1, xy.2))

theorem frp_mem_internalEdges {S : Finset (Site d)} {x y : Site d}
    (hx : x ∈ S) (hy : y ∈ S) : s(x, y) ∈ frpInternalEdges S :=
  Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩


theorem frp_connWithin_transfer (K : FiniteRangeKernel d)
    {omega omega' : ConfigSpace (Sym2 (Site d))} {S : Finset (Site d)}
    (hagree : ∀ e ∈ frpInternalEdges S, omega e = omega' e)
    {a b : (S : Set (Site d))}
    (h : ConnWithin (frpGraph K) omega (S : Set (Site d)) a b) :
    ConnWithin (frpGraph K) omega' (S : Set (Site d)) a b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v t hadj path ih =>
      have hopen' : (openSub (frpGraph K) omega').Adj (u : Site d) (v : Site d) := by
        refine ⟨hadj.1, ?_⟩
        rw [← hagree s((u : Site d), (v : Site d))
          (frp_mem_internalEdges u.2 v.2)]
        exact hadj.2
      exact (show ((openSub (frpGraph K) omega').induce
        (S : Set (Site d))).Adj u v from hopen').reachable.trans ih


theorem frp_connEvent_dependsOn (K : FiniteRangeKernel d)
    (S : Finset (Site d)) (u x : Site d) :
    DependsOn (connEvent (frpGraph K) (S : Set (Site d)) u {x})
      (frpInternalEdges S : Set (Sym2 (Site d))) := by
  intro omega omega' hagree
  constructor
  · rintro ⟨hu, z, hzS, hzx, hconn⟩
    simp only [Set.mem_singleton_iff] at hzx
    subst z
    exact ⟨hu, x, hzS, rfl,
      frp_connWithin_transfer K
        (fun e he => (hagree e (by exact_mod_cast he)).symm) hconn⟩
  · rintro ⟨hu, z, hzS, hzx, hconn⟩
    simp only [Set.mem_singleton_iff] at hzx
    subst z
    exact ⟨hu, x, hzS, rfl,
      frp_connWithin_transfer K
        (fun e he => hagree e (by exact_mod_cast he)) hconn⟩


theorem frp_connEvent_set_dependsOn (K : FiniteRangeKernel d)
    (S : Finset (Site d)) (u : Site d) (B : Set (Site d)) :
    DependsOn (connEvent (frpGraph K) (S : Set (Site d)) u B)
      (frpInternalEdges S : Set (Sym2 (Site d))) := by
  intro omega omega' hagree
  constructor
  · rintro ⟨hu, z, hzS, hzB, hconn⟩
    exact ⟨hu, z, hzS, hzB,
      frp_connWithin_transfer K
        (fun e he => (hagree e (by exact_mod_cast he)).symm) hconn⟩
  · rintro ⟨hu, z, hzS, hzB, hconn⟩
    exact ⟨hu, z, hzS, hzB,
      frp_connWithin_transfer K
        (fun e he => hagree e (by exact_mod_cast he)) hconn⟩


theorem frp_firstExit_inclusion (K : FiniteRangeKernel d)
    (A : Set (Site d)) (S : Finset (Site d)) (B : Set (Site d))
    (u : Site d) (huS : u ∈ S) (hBS : ∀ z ∈ B, z ∉ S) :
    connEvent (frpGraph K) A u B ⊆
      ⋃ q ∈ frpBoundaryPairs K S,
        disjointOccurrence
          (connEvent (frpGraph K) (S : Set (Site d)) u {q.1})
          (disjointOccurrence (edgeOpenEvent q.1 q.2)
            (connEvent (frpGraph K) A q.2 B)) := by
  intro omega homega
  simp only [connEvent, Set.mem_setOf_eq] at homega
  obtain ⟨b, hbA, hbB, path, hsupp⟩ :=
    shk_walk_of_connToSet (frpGraph K) omega A u B homega
  have hbypass_supp : ∀ z ∈ path.bypass.support, z ∈ A := fun z hz =>
    hsupp z (path.support_bypass_subset hz)
  have hbS : b ∉ (S : Set (Site d)) := hBS b hbB
  obtain ⟨x, y, hxS, hyS, hadj, htriple⟩ :=
    shk_firstExit_triple (frpGraph K) omega A (S : Set (Site d)) B
      u b huS hbB hbS path.bypass path.bypass_isPath hbypass_supp
  rw [Set.mem_iUnion₂]
  exact ⟨(x, y), (mem_frpBoundaryPairs K S).mpr ⟨hxS, hyS, hadj⟩, htriple⟩

private theorem frp_edgeOpen_dependsOn (x y : Site d) :
    DependsOn (edgeOpenEvent x y)
      ({s(x, y)} : Set (Sym2 (Site d))) := by
  intro omega omega' hagree
  change (omega s(x, y) = true) ↔ (omega' s(x, y) = true)
  rw [hagree s(x, y) (by simp)]


noncomputable def frpFirstExitSupport (K : FiniteRangeKernel d)
    (S Lam : Finset (Site d)) : Finset (Sym2 (Site d)) :=
  (frpInternalEdges S ∪
      (frpBoundaryPairs K S).image (fun q => s(q.1, q.2))) ∪
    frpInternalEdges Lam



theorem frp_bk_criterion (K : FiniteRangeKernel d) (beta : ℝ)
    (Lam S : Finset (Site d)) (u : Site d) (B : Set (Site d))
    (huS : u ∈ S) (hBS : ∀ z ∈ B, z ∉ S) :
    (frpMeasure K beta).real
        (connEvent (frpGraph K) (Lam : Set (Site d)) u B) ≤
      ∑ q ∈ frpBoundaryPairs K S,
        (frpEdgeParam K beta s(q.1, q.2) : ℝ) *
          (frpMeasure K beta).real
            (connEvent (frpGraph K) (S : Set (Site d)) u {q.1}) *
          (frpMeasure K beta).real
            (connEvent (frpGraph K) (Lam : Set (Site d)) q.2 B) := by
  classical
  let bnd := frpBoundaryPairs K S
  let P : Site d × Site d → Set (ConfigSpace (Sym2 (Site d))) := fun q =>
    connEvent (frpGraph K) (S : Set (Site d)) u {q.1}
  let Q : Site d × Site d → Set (ConfigSpace (Sym2 (Site d))) := fun q =>
    edgeOpenEvent q.1 q.2
  let R : Site d × Site d → Set (ConfigSpace (Sym2 (Site d))) := fun q =>
    connEvent (frpGraph K) (Lam : Set (Site d)) q.2 B
  let F := frpFirstExitSupport K S Lam
  have hPdep : ∀ q ∈ bnd, DependsOn (P q) (F : Set (Sym2 (Site d))) := by
    intro q _
    apply (frp_connEvent_dependsOn K S u q.1).mono
    intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
  have hQdep : ∀ q ∈ bnd, DependsOn (Q q) (F : Set (Sym2 (Site d))) := by
    intro q hq
    apply (frp_edgeOpen_dependsOn q.1 q.2).mono
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst e
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hRdep : ∀ q ∈ bnd, DependsOn (R q) (F : Set (Sym2 (Site d))) := by
    intro q _
    apply (frp_connEvent_set_dependsOn K Lam q.2 B).mono
    intro e he
    exact Finset.mem_union_right _ he
  have hcrit := inhom_bk_criterion_of_finite_dependsOn
    (frpEdgeParam K beta) (frpEdgeParam_le_one K beta)
    bnd P Q R F hPdep hQdep hRdep
    (fun q _ => isIncreasing_connEvent (frpGraph K) (S : Set (Site d)) u {q.1})
    (fun q _ => isIncreasing_edgeOpenEvent q.1 q.2)
    (fun q _ => isIncreasing_connEvent (frpGraph K) (Lam : Set (Site d)) q.2 B)
    (frp_firstExit_inclusion K (Lam : Set (Site d)) S B u huS hBS)
  change (frpMeasure K beta).real
      (connEvent (frpGraph K) (Lam : Set (Site d)) u B) ≤ _
  calc
    (frpMeasure K beta).real
        (connEvent (frpGraph K) (Lam : Set (Site d)) u B) ≤
        ∑ q ∈ bnd, (frpMeasure K beta).real (P q) *
          (frpMeasure K beta).real (Q q) *
          (frpMeasure K beta).real (R q) := hcrit
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [show (frpMeasure K beta).real (Q q) =
          (frpEdgeParam K beta s(q.1, q.2) : ℝ) by
        exact inhom_coord_true_prob (frpEdgeParam K beta)
          (frpEdgeParam_le_one K beta) s(q.1, q.2)]
      simp only [bnd, P, R]
      ring


noncomputable def frpPhi (K : FiniteRangeKernel d) (beta : ℝ)
    (S : Finset (Site d)) : ℝ :=
  ∑ q ∈ frpBoundaryPairs K S,
    (frpEdgeParam K beta s(q.1, q.2) : ℝ) *
      (frpMeasure K beta).real
        (connEvent (frpGraph K) (S : Set (Site d)) (0 : Site d) {q.1})


def frpCrossingEvent (K : FiniteRangeKernel d) (n : ℕ) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  connEvent (frpGraph K) Set.univ (0 : Site d) (box d (n - 1))ᶜ

noncomputable def frpCrossProb (K : FiniteRangeKernel d) (beta : ℝ)
    (n : ℕ) : ℝ :=
  (frpMeasure K beta).real (frpCrossingEvent K n)


theorem frp_adj_mem_box_add (K : FiniteRangeKernel d) {N : ℕ}
    {x y : Site d} (hx : x ∈ box d N) (hxy : (frpGraph K).Adj x y) :
    y ∈ box d (N + K.range) := by
  have hz := frpGraph_adj_displacement K hxy
  rw [mem_box] at hx hz ⊢
  intro i
  have heq : y = x + (y - x) := by abel
  have hadd : (y i).natAbs ≤ (x i).natAbs + ((y - x) i).natAbs := by
    conv_lhs => rw [heq, Pi.add_apply]
    exact Int.natAbs_add_le _ _
  exact hadd.trans (Nat.add_le_add (hx i) (hz i))


theorem frp_connWithin_mono_set (K : FiniteRangeKernel d)
    (omega : ConfigSpace (Sym2 (Site d))) {S T : Set (Site d)}
    (hST : S ⊆ T) {x y : S}
    (h : ConnWithin (frpGraph K) omega S x y) :
    ConnWithin (frpGraph K) omega T
      ⟨(x : Site d), hST x.2⟩ ⟨(y : Site d), hST y.2⟩ := by
  let f : ((openSub (frpGraph K) omega).induce S) →g
      ((openSub (frpGraph K) omega).induce T) :=
    { toFun := fun z => ⟨(z : Site d), hST z.2⟩
      map_rel' := fun {a b} hab => hab }
  exact h.map f



noncomputable def frpCrossingWindow (K : FiniteRangeKernel d) (n : ℕ) :
    Finset (Site d) :=
  (box_finite d ((n - 1) + K.range)).toFinset

@[simp] theorem mem_frpCrossingWindow (K : FiniteRangeKernel d) (n : ℕ)
    (x : Site d) :
    x ∈ frpCrossingWindow K n ↔ x ∈ box d ((n - 1) + K.range) := by
  rw [frpCrossingWindow, Set.Finite.mem_toFinset]




theorem frpCrossingEvent_eq_finite (K : FiniteRangeKernel d) (n : ℕ) :
    frpCrossingEvent K n =
      connEvent (frpGraph K) (frpCrossingWindow K n : Set (Site d))
        (0 : Site d) (box d (n - 1))ᶜ := by
  classical
  apply Set.Subset.antisymm
  · intro omega homega
    have h0 : (0 : Site d) ∈ (box_finite d (n - 1)).toFinset := by
      rw [Set.Finite.mem_toFinset, mem_box]
      intro i
      simp
    have hfirst := frp_firstExit_inclusion K Set.univ
      (box_finite d (n - 1)).toFinset (box d (n - 1))ᶜ
      (0 : Site d) h0 (by simp)
    obtain ⟨q, hq, htriple⟩ := Set.mem_iUnion₂.mp (hfirst homega)
    have hparts := disjointOccurrence_subset_inter _ _ htriple
    have htail := disjointOccurrence_subset_inter _ _ hparts.2
    rcases hparts.1 with ⟨h0S, x, hxS, hxeq, hconn⟩
    simp only [Set.mem_singleton_iff] at hxeq
    subst x
    have hqmem := (mem_frpBoundaryPairs K
      (box_finite d (n - 1)).toFinset).mp hq
    have hxbox : q.1 ∈ box d (n - 1) := by
      simpa [Set.Finite.mem_toFinset] using hqmem.1
    have hybox : q.2 ∈ box d ((n - 1) + K.range) :=
      frp_adj_mem_box_add K hxbox hqmem.2.2
    have hSsub : (box d (n - 1)) ⊆ box d ((n - 1) + K.range) :=
      box_mono d (Nat.le_add_right _ _)
    have hSsub' : ((box_finite d (n - 1)).toFinset : Set (Site d)) ⊆
        (frpCrossingWindow K n : Set (Site d)) := by
      intro z hz
      rw [Finset.mem_coe, mem_frpCrossingWindow]
      apply hSsub
      simpa [Set.Finite.mem_toFinset] using hz
    have hconn' := frp_connWithin_mono_set K omega hSsub' hconn
    have hedge : (openSub (frpGraph K) omega).Adj q.1 q.2 :=
      ⟨hqmem.2.2, htail.1⟩
    have hxwin : q.1 ∈ frpCrossingWindow K n :=
      (mem_frpCrossingWindow K n q.1).mpr (hSsub hxbox)
    have hywin : q.2 ∈ frpCrossingWindow K n :=
      (mem_frpCrossingWindow K n q.2).mpr hybox
    have hedge' : ((openSub (frpGraph K) omega).induce
        (frpCrossingWindow K n : Set (Site d))).Adj
        ⟨q.1, hxwin⟩ ⟨q.2, hywin⟩ := hedge
    have hyout : q.2 ∈ (box d (n - 1))ᶜ := by
      rw [Set.mem_compl_iff]
      intro hyin
      exact hqmem.2.1 (by simpa [Set.Finite.mem_toFinset] using hyin)
    refine ⟨?_, q.2, ?_, hyout, hconn'.trans hedge'.reachable⟩
    · rw [Finset.mem_coe, mem_frpCrossingWindow, mem_box]
      intro i
      simp
    · exact_mod_cast hywin
  · rintro omega ⟨h0, z, hz, hzout, hconn⟩
    refine ⟨Set.mem_univ _, z, Set.mem_univ _, hzout, ?_⟩
    exact frp_connWithin_mono_set K omega (Set.subset_univ _) hconn


theorem frpCrossingEvent_dependsOn (K : FiniteRangeKernel d) (n : ℕ) :
    DependsOn (frpCrossingEvent K n)
      (frpInternalEdges (frpCrossingWindow K n) : Set (Sym2 (Site d))) := by
  rw [frpCrossingEvent_eq_finite]
  exact frp_connEvent_set_dependsOn K (frpCrossingWindow K n)
    (0 : Site d) (box d (n - 1))ᶜ



noncomputable def frpOneStepClosure (K : FiniteRangeKernel d)
    (S : Finset (Site d)) : Finset (Site d) :=
  S ∪ (S ×ˢ frpSteps K).image (fun xz => xz.1 + xz.2)

theorem frp_subset_oneStepClosure (K : FiniteRangeKernel d)
    (S : Finset (Site d)) : S ⊆ frpOneStepClosure K S :=
  Finset.subset_union_left

theorem frp_boundary_snd_mem_closure (K : FiniteRangeKernel d)
    (S : Finset (Site d)) {q : Site d × Site d}
    (hq : q ∈ frpBoundaryPairs K S) : q.2 ∈ frpOneStepClosure K S := by
  have hm := (mem_frpBoundaryPairs K S).mp hq
  let z := q.2 - q.1
  have hz : z ∈ frpSteps K := (mem_frpSteps K).mpr hm.2.2
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨(q.1, z), Finset.mem_product.mpr ⟨hm.1, hz⟩, ?_⟩
  simp [z]



theorem frp_exitEvent_eq_finite (K : FiniteRangeKernel d)
    (S : Finset (Site d)) (u : Site d) (huS : u ∈ S) :
    connEvent (frpGraph K) Set.univ u (S : Set (Site d))ᶜ =
      connEvent (frpGraph K) (frpOneStepClosure K S : Set (Site d))
        u (S : Set (Site d))ᶜ := by
  classical
  apply Set.Subset.antisymm
  · intro omega homega
    have hfirst := frp_firstExit_inclusion K Set.univ S
      (S : Set (Site d))ᶜ u huS (by simp)
    obtain ⟨q, hq, htriple⟩ := Set.mem_iUnion₂.mp (hfirst homega)
    have hparts := disjointOccurrence_subset_inter _ _ htriple
    have htail := disjointOccurrence_subset_inter _ _ hparts.2
    rcases hparts.1 with ⟨hu, x, hxS, hxeq, hconn⟩
    simp only [Set.mem_singleton_iff] at hxeq
    subst x
    have hqm := (mem_frpBoundaryPairs K S).mp hq
    have hSsub : (S : Set (Site d)) ⊆
        (frpOneStepClosure K S : Set (Site d)) := by
      intro z hz
      exact_mod_cast frp_subset_oneStepClosure K S hz
    have hconn' := frp_connWithin_mono_set K omega hSsub hconn
    have hxcl : q.1 ∈ frpOneStepClosure K S :=
      frp_subset_oneStepClosure K S hqm.1
    have hycl : q.2 ∈ frpOneStepClosure K S :=
      frp_boundary_snd_mem_closure K S hq
    have hedge : (openSub (frpGraph K) omega).Adj q.1 q.2 :=
      ⟨hqm.2.2, htail.1⟩
    have hedge' : ((openSub (frpGraph K) omega).induce
        (frpOneStepClosure K S : Set (Site d))).Adj
        ⟨q.1, hxcl⟩ ⟨q.2, hycl⟩ := hedge
    refine ⟨?_, q.2, ?_, ?_, hconn'.trans hedge'.reachable⟩
    · exact_mod_cast frp_subset_oneStepClosure K S huS
    · exact_mod_cast hycl
    · rw [Set.mem_compl_iff]
      exact_mod_cast hqm.2.1
  · rintro omega ⟨hu, z, hz, hzout, hconn⟩
    exact ⟨Set.mem_univ _, z, Set.mem_univ _, hzout,
      frp_connWithin_mono_set K omega (Set.subset_univ _) hconn⟩

theorem frp_exitEvent_dependsOn (K : FiniteRangeKernel d)
    (S : Finset (Site d)) (u : Site d) (huS : u ∈ S) :
    DependsOn (connEvent (frpGraph K) Set.univ u (S : Set (Site d))ᶜ)
      (frpInternalEdges (frpOneStepClosure K S) : Set (Sym2 (Site d))) := by
  rw [frp_exitEvent_eq_finite K S u huS]
  exact frp_connEvent_set_dependsOn K (frpOneStepClosure K S) u
    (S : Set (Site d))ᶜ

theorem measurableSet_frp_exitEvent (K : FiniteRangeKernel d)
    (S : Finset (Site d)) (u : Site d) (huS : u ∈ S) :
    MeasurableSet (connEvent (frpGraph K) Set.univ u (S : Set (Site d))ᶜ) :=
  measurableSet_of_dependsOn
    (ih_indicator_dependsOn_of_event (frp_exitEvent_dependsOn K S u huS))


theorem frpGraph_adj_smul (K : FiniteRangeKernel d)
    (g : Multiplicative (Site d)) (x y : Site d) :
    (frpGraph K).Adj (g • x) (g • y) ↔ (frpGraph K).Adj x y := by
  have hcouple := frpEdgeCoupling_smul K g s(x, y)
  rw [smul_sym2_mk, frpEdgeCoupling_mk, frpEdgeCoupling_mk] at hcouple
  change 0 < K.coupling (g • y - g • x) ↔ 0 < K.coupling (y - x)
  rw [hcouple]

theorem frp_openSub_adj_shift (K : FiniteRangeKernel d)
    (g : Multiplicative (Site d))
    (omega : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    (openSub (frpGraph K) (shift g omega)).Adj (g • x) (g • y) ↔
      (openSub (frpGraph K) omega).Adj x y := by
  simp only [openSub]
  rw [frpGraph_adj_smul, shift_apply_smul]

private def frpTranslateHom (K : FiniteRangeKernel d)
    (g : Multiplicative (Site d)) (omega : ConfigSpace (Sym2 (Site d))) :
    openSub (frpGraph K) omega →g openSub (frpGraph K) (shift g omega) where
  toFun x := g • x
  map_rel' {x y} h := (frp_openSub_adj_shift K g omega x y).mpr h

private def frpTranslateHomInv (K : FiniteRangeKernel d)
    (g : Multiplicative (Site d)) (omega : ConfigSpace (Sym2 (Site d))) :
    openSub (frpGraph K) (shift g omega) →g openSub (frpGraph K) omega where
  toFun x := g⁻¹ • x
  map_rel' {x y} h := by
    have h' := (frp_openSub_adj_shift K g omega (g⁻¹ • x) (g⁻¹ • y)).mp
    simp only [smul_inv_smul] at h'
    exact h' h


theorem frp_connWithin_univ_shift (K : FiniteRangeKernel d)
    (g : Multiplicative (Site d)) (omega : ConfigSpace (Sym2 (Site d)))
    (x y : Site d) :
    ConnWithin (frpGraph K) (shift g omega) Set.univ
        ⟨g • x, Set.mem_univ _⟩ ⟨g • y, Set.mem_univ _⟩ ↔
      ConnWithin (frpGraph K) omega Set.univ
        ⟨x, Set.mem_univ _⟩ ⟨y, Set.mem_univ _⟩ := by
  constructor
  · intro h
    let f : ((openSub (frpGraph K) (shift g omega)).induce Set.univ) →g
        ((openSub (frpGraph K) omega).induce Set.univ) :=
      { toFun := fun z => ⟨g⁻¹ • (z : Site d), Set.mem_univ _⟩
        map_rel' := fun {a b} hab =>
          (frpTranslateHomInv K g omega).map_rel hab }
    convert h.map f using 1 <;> simp [f]
  · intro h
    let f : ((openSub (frpGraph K) omega).induce Set.univ) →g
        ((openSub (frpGraph K) (shift g omega)).induce Set.univ) :=
      { toFun := fun z => ⟨g • (z : Site d), Set.mem_univ _⟩
        map_rel' := fun {a b} hab => (frpTranslateHom K g omega).map_rel hab }
    exact h.map f


noncomputable def frpShiftedBox (y : Site d) (n : ℕ) : Finset (Site d) :=
  ((box_finite d (n - 1)).toFinset).image (fun z => z - y)

theorem mem_frpShiftedBox (y z : Site d) (n : ℕ) :
    z ∈ frpShiftedBox y n ↔ z + y ∈ box d (n - 1) := by
  classical
  rw [frpShiftedBox, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwbox : w ∈ box d (n - 1) := by
      simpa [Set.Finite.mem_toFinset] using hw
    simpa only [sub_add_cancel] using hwbox
  · intro hz
    refine ⟨z + y, ?_, ?_⟩
    · simpa [Set.Finite.mem_toFinset] using hz
    · simp

def frpCrossingEventFrom (K : FiniteRangeKernel d) (y : Site d) (n : ℕ) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  connEvent (frpGraph K) Set.univ y (box d (n - 1))ᶜ

theorem frpCrossingEventFrom_zero (K : FiniteRangeKernel d) (n : ℕ) :
    frpCrossingEventFrom K 0 n = frpCrossingEvent K n := rfl



theorem frpCrossingEventFrom_eq_preimage (K : FiniteRangeKernel d)
    (y : Site d) (n : ℕ) :
    frpCrossingEventFrom K y n =
      (shift (Multiplicative.ofAdd (-y)) : ConfigSpace (Sym2 (Site d)) → _) ⁻¹'
        connEvent (frpGraph K) Set.univ (0 : Site d)
          (frpShiftedBox y n : Set (Site d))ᶜ := by
  ext omega
  set g := Multiplicative.ofAdd (-y) with hg
  have hgy : g • y = (0 : Site d) := by
    funext i
    show -y i + y i = (0 : ℤ)
    ring
  constructor
  · rintro ⟨_, v, _, hvout, hconn⟩
    refine ⟨Set.mem_univ _, g • v, Set.mem_univ _, ?_, ?_⟩
    · rw [Set.mem_compl_iff, Finset.mem_coe, mem_frpShiftedBox]
      have heq : g • v + y = v := by
        funext i
        show (-y i + v i) + y i = v i
        ring
      rwa [heq]
    · have hs := (frp_connWithin_univ_shift K g omega y v).mpr hconn
      rwa [hgy] at hs
  · rintro ⟨_, w, _, hwout, hconn⟩
    refine ⟨Set.mem_univ _, g⁻¹ • w, Set.mem_univ _, ?_, ?_⟩
    · rw [Set.mem_compl_iff, Finset.mem_coe, mem_frpShiftedBox] at hwout
      have hgi : g⁻¹ • w = w + y := by
        funext i
        rw [smul_site_apply]
        simp only [hg, ← ofAdd_neg, toAdd_ofAdd, neg_neg, Pi.add_apply]
        ring
      rwa [hgi]
    · have hs := (frp_connWithin_univ_shift K g omega y (g⁻¹ • w)).mp ?_
      · exact hs
      · rw [hgy, smul_inv_smul]
        exact hconn


theorem frp_crossProbFrom_le (K : FiniteRangeKernel d) (beta : ℝ)
    (y : Site d) {L m n : ℕ} (hy : y ∈ box d L)
    (hmLn : m + L ≤ n) (hm : 1 ≤ m) :
    (frpMeasure K beta).real (frpCrossingEventFrom K y n) ≤
      frpCrossProb K beta m := by
  let mu := frpMeasure K beta
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, frpMeasure]
    infer_instance
  let g := Multiplicative.ofAdd (-y)
  let B := connEvent (frpGraph K) Set.univ (0 : Site d)
    (frpShiftedBox y n : Set (Site d))ᶜ
  have hyinner : y ∈ box d (n - 1) := by
    apply box_mono d (show L ≤ n - 1 by omega)
    exact hy
  have h0B : (0 : Site d) ∈ frpShiftedBox y n := by
    rw [mem_frpShiftedBox]
    simpa using hyinner
  have hBmeas : MeasurableSet B :=
    measurableSet_frp_exitEvent K (frpShiftedBox y n) 0 h0B
  have hpres := (frpMeasure_translationInvariant K beta) g
  have hstep : mu.real (frpCrossingEventFrom K y n) = mu.real B := by
    rw [frpCrossingEventFrom_eq_preimage]
    exact hpres.measureReal_preimage hBmeas.nullMeasurableSet
  rw [hstep]
  have hsub : B ⊆ frpCrossingEvent K m := by
    rintro omega ⟨_, v, _, hvout, hconn⟩
    refine ⟨Set.mem_univ _, v, Set.mem_univ _, ?_, hconn⟩
    rw [Set.mem_compl_iff]
    intro hvm
    apply hvout
    rw [Finset.mem_coe, mem_frpShiftedBox]
    exact box_shift_mem hy hvm hmLn hm
  exact measureReal_mono hsub (measure_ne_top _ _)

theorem frpCrossProb_nonneg (K : FiniteRangeKernel d) (beta : ℝ) (n : ℕ) :
    0 ≤ frpCrossProb K beta n := measureReal_nonneg

theorem frpCrossProb_le_one (K : FiniteRangeKernel d) (beta : ℝ) (n : ℕ) :
    frpCrossProb K beta n ≤ 1 := by
  unfold frpCrossProb
  rw [show (1 : ℝ) = (frpMeasure K beta).real Set.univ by rw [probReal_univ]]
  exact measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)

theorem frpCrossingEvent_antitone (K : FiniteRangeKernel d) {m n : ℕ}
    (hmn : m ≤ n) : frpCrossingEvent K n ⊆ frpCrossingEvent K m := by
  rintro omega ⟨_, z, _, hzout, hconn⟩
  refine ⟨Set.mem_univ _, z, Set.mem_univ _, ?_, hconn⟩
  rw [Set.mem_compl_iff] at hzout ⊢
  intro hzm
  exact hzout (box_mono d (by omega) hzm)

theorem frpCrossProb_antitone (K : FiniteRangeKernel d) (beta : ℝ) :
    Antitone (frpCrossProb K beta) := fun _ _ hmn =>
  measureReal_mono (frpCrossingEvent_antitone K hmn) (measure_ne_top _ _)



theorem frp_subcritical_oneStep (K : FiniteRangeKernel d) (beta : ℝ)
    (S : Finset (Site d)) (h0S : (0 : Site d) ∈ S)
    (L : ℕ) (hL : 1 ≤ L) (hRL : K.range ≤ L)
    (hSbox : (S : Set (Site d)) ⊆ box d (L - K.range))
    (k : ℕ) (hk : 1 ≤ k) :
    frpCrossProb K beta ((k + 1) * L) ≤
      frpPhi K beta S * frpCrossProb K beta (k * L) := by
  classical
  let n := (k + 1) * L
  let m := k * L
  let T : Finset (Site d) := (box_finite d (n - 1)).toFinset
  let Lam := frpOneStepClosure K T
  let B : Set (Site d) := (box d (n - 1))ᶜ
  have hm1 : 1 ≤ m := by simp only [m]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmn : m + L = n := by simp [m, n, Nat.add_mul]
  have h0T : (0 : Site d) ∈ T := by
    simp only [T, Set.Finite.mem_toFinset, mem_box]
    intro i
    simp
  have hST : (S : Set (Site d)) ⊆ (T : Set (Site d)) := by
    intro z hz
    change z ∈ (box_finite d (n - 1)).toFinset
    rw [Set.Finite.mem_toFinset]
    apply box_mono d (show L - K.range ≤ n - 1 by
      simp only [n]
      omega)
    exact hSbox hz
  have hBS : ∀ z ∈ B, z ∉ S := by
    intro z hzout hzS
    apply hzout
    change z ∈ box d (n - 1)
    rw [← show (T : Set (Site d)) = box d (n - 1) by
      ext w
      simp only [T, Finset.mem_coe, Set.Finite.mem_toFinset]]
    exact hST (by exact_mod_cast hzS)
  have hbk := frp_bk_criterion K beta Lam S (0 : Site d) B h0S hBS
  have hTcoe : (T : Set (Site d)) = box d (n - 1) := by
    ext z
    simp only [T, Finset.mem_coe, Set.Finite.mem_toFinset]
  have hleft :
      (frpMeasure K beta).real
          (connEvent (frpGraph K) (Lam : Set (Site d)) (0 : Site d) B) =
        frpCrossProb K beta n := by
    unfold Lam B frpCrossProb frpCrossingEvent
    rw [← hTcoe, ← frp_exitEvent_eq_finite K T 0 h0T]
  rw [hleft] at hbk
  calc
    frpCrossProb K beta n ≤
        ∑ q ∈ frpBoundaryPairs K S,
          (frpEdgeParam K beta s(q.1, q.2) : ℝ) *
            (frpMeasure K beta).real
              (connEvent (frpGraph K) (S : Set (Site d)) 0 {q.1}) *
            frpCrossProb K beta m := by
      refine hbk.trans (Finset.sum_le_sum fun q hq => ?_)
      have hqm := (mem_frpBoundaryPairs K S).mp hq
      have hxbox : q.1 ∈ box d (L - K.range) := hSbox (by exact_mod_cast hqm.1)
      have hybox0 : q.2 ∈ box d ((L - K.range) + K.range) :=
        frp_adj_mem_box_add K hxbox hqm.2.2
      have hybox : q.2 ∈ box d L := by
        rwa [Nat.sub_add_cancel hRL] at hybox0
      have htailSub :
          connEvent (frpGraph K) (Lam : Set (Site d)) q.2 B ⊆
            frpCrossingEventFrom K q.2 n := by
        rintro omega ⟨hy, z, hz, hzB, hconn⟩
        exact ⟨Set.mem_univ _, z, Set.mem_univ _, hzB,
          frp_connWithin_mono_set K omega (Set.subset_univ _) hconn⟩
      have htail :
          (frpMeasure K beta).real
              (connEvent (frpGraph K) (Lam : Set (Site d)) q.2 B) ≤
            frpCrossProb K beta m :=
        (measureReal_mono htailSub (measure_ne_top _ _)).trans
          (frp_crossProbFrom_le K beta q.2 hybox hmn.le hm1)
      have hcoef : 0 ≤
          (frpEdgeParam K beta s(q.1, q.2) : ℝ) *
            (frpMeasure K beta).real
              (connEvent (frpGraph K) (S : Set (Site d)) 0 {q.1}) :=
        mul_nonneg (frpEdgeParam K beta s(q.1, q.2)).coe_nonneg measureReal_nonneg
      exact mul_le_mul_of_nonneg_left htail hcoef
    _ = frpPhi K beta S * frpCrossProb K beta m := by
      unfold frpPhi
      rw [Finset.sum_mul]

theorem frpPhi_nonneg (K : FiniteRangeKernel d) (beta : ℝ)
    (S : Finset (Site d)) : 0 ≤ frpPhi K beta S := by
  unfold frpPhi
  apply Finset.sum_nonneg
  intro q _
  exact mul_nonneg (frpEdgeParam K beta s(q.1, q.2)).coe_nonneg
    measureReal_nonneg



theorem frp_subcritical_geometric (K : FiniteRangeKernel d) (beta : ℝ)
    (S : Finset (Site d)) (h0S : (0 : Site d) ∈ S)
    (hphi : frpPhi K beta S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hRL : K.range ≤ L)
    (hSbox : (S : Set (Site d)) ⊆ box d (L - K.range)) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ k,
      frpCrossProb K beta (k * L) ≤ r⁻¹ * r ^ k := by
  let g : ℕ → ℝ := fun k => frpCrossProb K beta ((k + 1) * L)
  have hgnn : ∀ k, 0 ≤ g k := fun k => frpCrossProb_nonneg K beta _
  have hg0 : g 0 ≤ 1 := by
    simpa [g] using frpCrossProb_le_one K beta ((0 + 1) * L)
  have hgrec : ∀ k, g (k + 1) ≤ frpPhi K beta S * g k := by
    intro k
    have hstep := frp_subcritical_oneStep K beta S h0S L hL hRL hSbox
      (k + 1) (by omega)
    simp only [g]
    convert hstep using 2
  obtain ⟨r, hr0, hr1, hgrec'⟩ := step_with_pos_ratio hgnn hphi hgrec
  have hsubg : ∀ k, g k ≤ r ^ k := recursion_le_pow hg0 hr0.le hgrec'
  refine ⟨r, hr0, hr1, fun k => ?_⟩
  cases k with
  | zero =>
      simp only [Nat.zero_mul, pow_zero, mul_one]
      have h1 : frpCrossProb K beta 0 ≤ 1 := frpCrossProb_le_one K beta 0
      have h2 : (1 : ℝ) ≤ r⁻¹ := by
        rw [one_le_inv_iff₀]
        exact ⟨hr0, hr1.le⟩
      linarith
  | succ j =>
      have hj : frpCrossProb K beta ((j + 1) * L) ≤ r ^ j := hsubg j
      rw [show r⁻¹ * r ^ (j + 1) = r ^ j from by field_simp; ring]
      exact hj




theorem frp_subcritical_decay (K : FiniteRangeKernel d) (beta : ℝ)
    (S : Finset (Site d)) (h0S : (0 : Site d) ∈ S)
    (hphi : frpPhi K beta S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hRL : K.range ≤ L)
    (hSbox : (S : Set (Site d)) ⊆ box d (L - K.range)) :
    ∃ c > 0, ∃ C > 0, ∀ n,
      frpCrossProb K beta n ≤ C * Real.exp (-c * n) := by
  obtain ⟨r, hr0, hr1, hsub⟩ :=
    frp_subcritical_geometric K beta S h0S hphi L hL hRL hSbox
  exact geometric_subseq_antitone_decay' hL hr0 hr1 (by positivity)
    (frpCrossProb_antitone K beta) hsub

theorem frpEdgeParam_eq_zero_of_nonpos (K : FiniteRangeKernel d)
    {beta : ℝ} (hbeta : beta ≤ 0) (e : Sym2 (Site d)) :
    frpEdgeParam K beta e = 0 := by
  unfold frpEdgeParam
  rw [Real.toNNReal_eq_zero]
  have hJ := K.nonneg
  have hexp : 1 ≤ Real.exp (-beta * frpEdgeCoupling K e) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg (neg_nonneg.mpr hbeta)
      (by
        induction e using Sym2.inductionOn with
        | _ x y => exact K.nonneg (y - x)))
  linarith

theorem frpPhi_eq_zero_of_nonpos (K : FiniteRangeKernel d)
    {beta : ℝ} (hbeta : beta ≤ 0) (S : Finset (Site d)) :
    frpPhi K beta S = 0 := by
  unfold frpPhi
  apply Finset.sum_eq_zero
  intro q _
  rw [frpEdgeParam_eq_zero_of_nonpos K hbeta]
  simp




def frpSubcriticalSet (K : FiniteRangeKernel d) : Set ℝ :=
  {beta | 0 ≤ beta ∧ ∀ gamma, 0 ≤ gamma → gamma ≤ beta →
    ∃ S : Finset (Site d), (0 : Site d) ∈ S ∧ frpPhi K gamma S < 1}

noncomputable def frpTildeBetaC (K : FiniteRangeKernel d) : ℝ :=
  sSup (frpSubcriticalSet K)

theorem frpSubcriticalSet_nonempty (K : FiniteRangeKernel d) :
    (frpSubcriticalSet K).Nonempty := by
  refine ⟨0, le_rfl, ?_⟩
  intro gamma hgamma0 hgamma
  have hgamma' : gamma = 0 := by linarith
  subst gamma
  refine ⟨{0}, by simp, ?_⟩
  rw [frpPhi_eq_zero_of_nonpos K le_rfl]
  norm_num



theorem exists_frpPhi_witness_of_lt_tildeBetaC (K : FiniteRangeKernel d)
    {beta : ℝ} (hbeta : beta < frpTildeBetaC K) :
    ∃ S : Finset (Site d), (0 : Site d) ∈ S ∧ frpPhi K beta S < 1 := by
  by_cases hb0 : beta < 0
  · refine ⟨{0}, by simp, ?_⟩
    rw [frpPhi_eq_zero_of_nonpos K hb0.le]
    norm_num
  · have hb0' : 0 ≤ beta := le_of_not_gt hb0
    unfold frpTildeBetaC at hbeta
    obtain ⟨gamma, hgamma, hbg⟩ :=
      exists_lt_of_lt_csSup (frpSubcriticalSet_nonempty K) hbeta
    exact hgamma.2 beta hb0' hbg.le







theorem frp_subcritical_decay_of_lt_tildeBetaC (K : FiniteRangeKernel d)
    {beta : ℝ} (hbeta : beta < frpTildeBetaC K) :
    ∃ c > 0, ∃ C > 0, ∀ n,
      frpCrossProb K beta n ≤ C * Real.exp (-c * n) := by
  obtain ⟨S, h0S, hphi⟩ := exists_frpPhi_witness_of_lt_tildeBetaC K hbeta
  obtain ⟨N, hSN⟩ := frp_finset_subset_box S
  let L := N + K.range + 1
  have hL : 1 ≤ L := by simp [L]
  have hRL : K.range ≤ L := by
    dsimp [L]
    omega
  have hsub : (S : Set (Site d)) ⊆ box d (L - K.range) := by
    have hcalc : L - K.range = N + 1 := by
      dsimp [L]
      omega
    rw [hcalc]
    exact hSN.trans (box_mono d (Nat.le_succ N))
  exact frp_subcritical_decay K beta S h0S hphi L hL hRL hsub

end Sharpness
end StatMech
