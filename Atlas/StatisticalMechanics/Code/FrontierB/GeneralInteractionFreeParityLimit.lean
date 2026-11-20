/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierB.GeneralInteractionFreeSpinLimit
import Code.FrontierB.InhomogeneousParityAvoidance
import Code.FrontierB.PlusBoxCurrentParity









open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff

namespace StatMech.FrontierB

open Sharpness Ising Lattice

def sym2MapEmbedding {V W : Type*} (f : V ↪ W) : Sym2 V ↪ Sym2 W where
  toFun := Sym2.map f
  inj' := Sym2.map.injective f.injective

noncomputable def sym2FinsetMap {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (E : Finset (Sym2 V)) : Finset (Sym2 W) :=
  E.map (sym2MapEmbedding f)

theorem sym2_toFinset_map_embedding {V W : Type*}
    [DecidableEq V] [DecidableEq W] (f : V ↪ W) (e : Sym2 V) :
    (Sym2.map f e).toFinset = e.toFinset.map f := by
  ext y
  simp

theorem finset_map_symmDiff {V W : Type*}
    [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (A B : Finset V) :
    (A ∆ B).map f = A.map f ∆ B.map f := by
  ext y
  simp only [Finset.mem_map, Finset.mem_symmDiff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨hA, hB⟩ | ⟨hB, hA⟩
    · exact Or.inl ⟨⟨x, hA, rfl⟩,
        fun ⟨z, hz, heq⟩ => hB (by simpa [f.injective heq] using hz)⟩
    · exact Or.inr ⟨⟨x, hB, rfl⟩,
        fun ⟨z, hz, heq⟩ => hA (by simpa [f.injective heq] using hz)⟩
  · rintro (⟨⟨x, hA, rfl⟩, hB⟩ | ⟨⟨x, hB, rfl⟩, hA⟩)
    · exact ⟨x, Or.inl ⟨hA, fun hx => hB ⟨x, hx, rfl⟩⟩, rfl⟩
    · exact ⟨x, Or.inr ⟨hB, fun hx => hA ⟨x, hx, rfl⟩⟩, rfl⟩


theorem edgeBoundary_sym2FinsetMap {V W : Type*}
    [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (E : Finset (Sym2 V)) :
    edgeBoundary (sym2FinsetMap f E) = (edgeBoundary E).map f := by
  classical
  induction E using Finset.induction with
  | empty => simp [sym2FinsetMap, edgeBoundary]
  | @insert e E he ih =>
      have hmap : Sym2.map f e ∉ sym2FinsetMap f E := by
        intro h
        rw [sym2FinsetMap, Finset.mem_map] at h
        obtain ⟨e', he', heq⟩ := h
        exact he (Sym2.map.injective f.injective heq.symm ▸ he')
      have hleft :
          edgeBoundary (sym2FinsetMap f (insert e E)) =
            (Sym2.map f e).toFinset ∆
              edgeBoundary (sym2FinsetMap f E) := by
        have hmap' : (sym2MapEmbedding f) e ∉
            Finset.map (sym2MapEmbedding f) E := by
          intro hm
          apply hmap
          exact hm
        unfold sym2FinsetMap edgeBoundary
        rw [Finset.map_insert, Finset.fold_insert hmap']
        rfl
      have hright :
          edgeBoundary (insert e E) = e.toFinset ∆ edgeBoundary E := by
        unfold edgeBoundary
        rw [Finset.fold_insert he]
      rw [hleft, hright, ih, sym2_toFinset_map_embedding,
        finset_map_symmDiff]


def interactionBoxLiftEdge {d n : Nat} (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (e : ↑F) : Sym2 (interactionBoxVertices d n) :=
  e.1.attachWith (fun x hx => mem_interactionBoxVertices.mpr
    (hFbox e.1 e.2 x hx))

@[simp] theorem interactionBoxLiftEdge_map_val {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (e : ↑F) :
    Sym2.map Subtype.val (interactionBoxLiftEdge F hFbox e) = e.1 := by
  exact Sym2.attachWith_map_subtypeVal
    (fun x hx => mem_interactionBoxVertices.mpr
      (hFbox e.1 e.2 x hx))

def interactionBoxLiftEdgeEmbedding {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n) :
    ↑F ↪ Sym2 (interactionBoxVertices d n) where
  toFun := interactionBoxLiftEdge F hFbox
  inj' e f hef := by
    apply Subtype.ext
    have h := congrArg (Sym2.map Subtype.val) hef
    simpa using h

noncomputable def interactionBoxLiftedEdges {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n) :
    Finset (Sym2 (interactionBoxVertices d n)) :=
  Finset.univ.map (interactionBoxLiftEdgeEmbedding F hFbox)

theorem interactionBoxLiftedEdges_ambient_image {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n) :
    sym2FinsetMap (Function.Embedding.subtype
      (fun x : Site d => x ∈ interactionBoxVertices d n))
      (interactionBoxLiftedEdges F hFbox) = F := by
  unfold sym2FinsetMap interactionBoxLiftedEdges
  rw [Finset.map_map]
  have hemb :
      (interactionBoxLiftEdgeEmbedding F hFbox).trans
          (sym2MapEmbedding (Function.Embedding.subtype
            (fun x : Site d => x ∈ interactionBoxVertices d n))) =
        (⟨Subtype.val, Subtype.val_injective⟩ : ↑F ↪ Sym2 (Site d)) := by
    apply Function.Embedding.ext
    intro e
    exact interactionBoxLiftEdge_map_val F hFbox e
  rw [hemb]
  ext e
  simp

theorem interactionBoxLiftedEdges_subset_edgeFinset {d n : Nat}
    (F : Finset (Sym2 (Site d)))
    (hFbox : ∀ e ∈ F, ∀ x ∈ e, x ∈ box d n)
    (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
    interactionBoxLiftedEdges F hFbox ⊆
      (interactionBoxGraph d n).edgeFinset := by
  intro e he
  rw [SimpleGraph.mem_edgeFinset]
  have hsource : ¬(Sym2.map Subtype.val e).IsDiag := by
    rw [interactionBoxLiftedEdges, Finset.mem_map] at he
    obtain ⟨g, hg, rfl⟩ := he
    change ¬(Sym2.map Subtype.val
      (interactionBoxLiftEdge F hFbox g)).IsDiag
    rw [interactionBoxLiftEdge_map_val]
    exact hFdiag g.1 g.2
  have hnonDiag : ¬e.IsDiag := by
    simpa only [Sym2.isDiag_map Subtype.val_injective] using hsource
  simpa [interactionBoxGraph] using hnonDiag

theorem preimage_currentParityAvoidCylinder_extendInteractionBoxCurrent
    (d n : Nat) (E : Finset (Sym2 (interactionBoxVertices d n)))
    (hE : E ⊆ (interactionBoxGraph d n).edgeFinset) :
    extendInteractionBoxCurrent d n ⁻¹'
        currentParityAvoidCylinder
          (sym2FinsetMap (Function.Embedding.subtype
            (fun x : Site d => x ∈ interactionBoxVertices d n)) E) =
      {m | Disjoint (currentParitySupport (interactionBoxGraph d n) m) E} := by
  ext m
  simp only [Set.mem_preimage, currentParityAvoidCylinder, Set.mem_setOf_eq]
  rw [Finset.disjoint_left]
  constructor
  · intro hall e heOdd heE'
    let i : (interactionBoxGraph d n).edgeFinset := ⟨e, hE heE'⟩
    have hodd : Odd (m i) := by
      exact (mem_currentParitySupport (interactionBoxGraph d n) m i).mp heOdd
    have hamb : Sym2.map Subtype.val e ∈
        sym2FinsetMap (Function.Embedding.subtype
          (fun x : Site d => x ∈ interactionBoxVertices d n)) E := by
      unfold sym2FinsetMap
      exact Finset.mem_map.mpr ⟨e, heE', rfl⟩
    have heven := hall (Sym2.map Subtype.val e) hamb
    have heq : extendInteractionBoxCurrent d n m
        (Sym2.map Subtype.val e) = m i := by
      exact extendInteractionBoxCurrent_included d n m i
    rw [heq] at heven
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  · intro hdis a ha
    unfold sym2FinsetMap at ha
    rw [Finset.mem_map] at ha
    obtain ⟨e, heE', rfl⟩ := ha
    let i : (interactionBoxGraph d n).edgeFinset := ⟨e, hE heE'⟩
    have hnotOdd : ¬Odd (m i) := by
      intro hodd
      exact (hdis
        ((mem_currentParitySupport (interactionBoxGraph d n) m i).mpr hodd)) heE'
    have heven : Even (m i) := Nat.not_odd_iff_even.mp hnotOdd
    change Even (extendInteractionBoxCurrent d n m
      (interactionBoxEdgeIncl d n i))
    rw [extendInteractionBoxCurrent_included d n m i]
    exact heven

theorem measurableSet_currentParityAvoidCylinder {E : Type*} [Countable E]
    (F : Finset E) : MeasurableSet (currentParityAvoidCylinder F) := by
  have hset : currentParityAvoidCylinder F =
      (restrictCurrent F) ⁻¹' {a : ↑F → Nat | ∀ e, Even (a e)} := by
    ext m
    simp [currentParityAvoidCylinder, restrictCurrent]
  rw [hset]
  exact (continuous_restrictCurrent F).measurable MeasurableSet.of_discrete



theorem generalFreeBoxCurrentMeasure_parityAvoid_edgeImage {d n : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (E : Finset (Sym2 (interactionBoxVertices d n)))
    (hE : E ⊆ (interactionBoxGraph d n).edgeFinset) :
    (generalFreeBoxCurrentMeasure J hJ n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder
          (sym2FinsetMap (Function.Embedding.subtype
            (fun x : Site d => x ∈ interactionBoxVertices d n)) E)) =
      ENNReal.ofReal
        (expJ (interactionBoxGraph d n).edgeFinset
            (fun e => beta * interactionBoxCoupling J n e) (fun _ => 0)
            (fun s => Real.exp (-weightedEdgeSpinSum beta
              (interactionBoxCoupling J n) E s)) *
          ∏ e ∈ E, Real.cosh
            (beta * interactionBoxCoupling J n e)) := by
  let A := sym2FinsetMap (Function.Embedding.subtype
    (fun x : Site d => x ∈ interactionBoxVertices d n)) E
  have hmeas : MeasurableSet (currentParityAvoidCylinder A) :=
    measurableSet_currentParityAvoidCylinder A
  calc
    (generalFreeBoxCurrentMeasure J hJ n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder A) =
      (sourcelessCurrentPMF (interactionBoxGraph d n) beta
        (interactionBoxCoupling J n) hbeta.le
          (fun e => hJ (Sym2.map Subtype.val e))).toMeasure
        {m | Disjoint (currentParitySupport (interactionBoxGraph d n) m) E} := by
      change Measure.map (extendInteractionBoxCurrent d n)
        (sourcelessCurrentPMF (interactionBoxGraph d n) beta
          (interactionBoxCoupling J n) hbeta.le
            (fun e => hJ (Sym2.map Subtype.val e))).toMeasure
          (currentParityAvoidCylinder A) = _
      rw [Measure.map_apply (measurable_extendInteractionBoxCurrent d n) hmeas,
        preimage_currentParityAvoidCylinder_extendInteractionBoxCurrent
          d n E hE]
    _ = ENNReal.ofReal
        (inhomogeneousParityAvoidSum (interactionBoxGraph d n) beta
            (interactionBoxCoupling J n) E /
          inhomogeneousParityPartition (interactionBoxGraph d n) beta
            (interactionBoxCoupling J n)) :=
      sourcelessCurrentMeasure_parityAvoid_inhomogeneous
        (interactionBoxGraph d n) beta hbeta
        (interactionBoxCoupling J n)
        (fun e => hJ (Sym2.map Subtype.val e)) E
    _ = _ := by
      rw [inhomogeneousParityAvoidRatio_eq_expJ
        (interactionBoxGraph d n) beta (interactionBoxCoupling J n) E hE]

noncomputable def interactionBoxTransportedEdges (d : Nat) {n m : Nat}
    (hnm : n ≤ m) (E : Finset (Sym2 (interactionBoxVertices d n))) :
    Finset (Sym2 (interactionBoxVertices d m)) :=
  sym2FinsetMap (interactionBoxVertexIncl d hnm) E

theorem interactionBoxTransportedEdges_subset_edgeFinset (d : Nat)
    {n m : Nat} (hnm : n ≤ m)
    (E : Finset (Sym2 (interactionBoxVertices d n)))
    (hE : E ⊆ (interactionBoxGraph d n).edgeFinset) :
    interactionBoxTransportedEdges d hnm E ⊆
      (interactionBoxGraph d m).edgeFinset := by
  intro e he
  unfold interactionBoxTransportedEdges sym2FinsetMap at he
  rw [Finset.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [SimpleGraph.mem_edgeFinset]
  have hnonDiag : ¬f.IsDiag :=
    (interactionBoxGraph d n).not_isDiag_of_mem_edgeFinset (hE hf)
  have hmapped : ¬(Sym2.map (interactionBoxVertexIncl d hnm) f).IsDiag := by
    simpa only [Sym2.isDiag_map (interactionBoxVertexIncl d hnm).injective]
      using hnonDiag
  simpa [interactionBoxGraph] using hmapped

theorem interactionBoxTransportedEdges_ambient_image (d : Nat)
    {n m : Nat} (hnm : n ≤ m)
    (E : Finset (Sym2 (interactionBoxVertices d n))) :
    sym2FinsetMap (Function.Embedding.subtype
      (fun x : Site d => x ∈ interactionBoxVertices d m))
      (interactionBoxTransportedEdges d hnm E) =
    sym2FinsetMap (Function.Embedding.subtype
      (fun x : Site d => x ∈ interactionBoxVertices d n)) E := by
  unfold interactionBoxTransportedEdges sym2FinsetMap
  rw [Finset.map_map]
  apply congrArg (fun f : Sym2 (interactionBoxVertices d n) ↪
    Sym2 (Site d) => E.map f)
  apply Function.Embedding.ext
  intro e
  induction e using Sym2.inductionOn with
  | _ x y => rfl

theorem interactionBoxSpinSupport_map_base (d : Nat) {n m : Nat}
    (hnm : n ≤ m) (A : Finset (interactionBoxVertices d n)) :
    interactionBoxSpinSupport d m
        (A.map (Function.Embedding.subtype
          (fun x : Site d => x ∈ interactionBoxVertices d n))) =
      A.map (interactionBoxVertexIncl d hnm) := by
  ext x
  simp only [interactionBoxSpinSupport, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, hval⟩
    refine ⟨a, ha, ?_⟩
    apply Subtype.ext
    exact hval
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

theorem interactionBoxCoupling_transport {d : Nat}
    (J : Sym2 (Site d) → ℝ) {n m : Nat} (hnm : n ≤ m)
    (e : Sym2 (interactionBoxVertices d n)) :
    interactionBoxCoupling J m
        (Sym2.map (interactionBoxVertexIncl d hnm) e) =
      interactionBoxCoupling J n e := by
  induction e using Sym2.inductionOn with
  | _ x y => rfl

theorem bond_transport {d : Nat} {n m : Nat} (hnm : n ≤ m)
    (s : ConfigSpace (interactionBoxVertices d m))
    (e : Sym2 (interactionBoxVertices d n)) :
    bond s (Sym2.map (interactionBoxVertexIncl d hnm) e) =
      bond (fun x => s (interactionBoxVertexIncl d hnm x)) e := by
  induction e using Sym2.inductionOn with
  | _ x y => rfl

theorem spinProd_transport {d : Nat} {n m : Nat} (hnm : n ≤ m)
    (s : ConfigSpace (interactionBoxVertices d m))
    (A : Finset (interactionBoxVertices d n)) :
    spinProd A (fun x => s (interactionBoxVertexIncl d hnm x)) =
      spinProd (A.map (interactionBoxVertexIncl d hnm)) s := by
  unfold spinProd
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro x hx
  rfl

theorem weightedEdgeSpinSum_transport {d : Nat}
    (J : Sym2 (Site d) → ℝ) (beta : ℝ) {n m : Nat}
    (hnm : n ≤ m) (E : Finset (Sym2 (interactionBoxVertices d n)))
    (s : ConfigSpace (interactionBoxVertices d m)) :
    weightedEdgeSpinSum beta (interactionBoxCoupling J m)
        (interactionBoxTransportedEdges d hnm E) s =
      weightedEdgeSpinSum beta (interactionBoxCoupling J n) E
        (fun x => s (interactionBoxVertexIncl d hnm x)) := by
  unfold weightedEdgeSpinSum interactionBoxTransportedEdges sym2FinsetMap
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e he
  change beta * interactionBoxCoupling J m
      (Sym2.map (interactionBoxVertexIncl d hnm) e) *
        bond s (Sym2.map (interactionBoxVertexIncl d hnm) e) = _
  rw [interactionBoxCoupling_transport J hnm,
    bond_transport hnm]



theorem exp_neg_weightedEdgeSpinSum_transport_expansion {d : Nat}
    (J : Sym2 (Site d) → ℝ) (beta : ℝ) {n m : Nat}
    (hnm : n ≤ m) (E : Finset (Sym2 (interactionBoxVertices d n)))
    (hEdiag : ∀ e ∈ E, ¬e.IsDiag)
    (s : ConfigSpace (interactionBoxVertices d m)) :
    Real.exp (-weightedEdgeSpinSum beta (interactionBoxCoupling J m)
        (interactionBoxTransportedEdges d hnm E) s) =
      ∑ T ∈ E.powerset,
        weightedEdgeExpansionCoeff beta (interactionBoxCoupling J n) E T *
          spinProd ((edgeBoundary (E \ T)).map
            (interactionBoxVertexIncl d hnm)) s := by
  rw [weightedEdgeSpinSum_transport J beta hnm E s,
    exp_neg_weightedEdgeSpinSum_eq_spinProd_sum
      beta (interactionBoxCoupling J n) E hEdiag]
  apply Finset.sum_congr rfl
  intro T hT
  rw [spinProd_transport hnm]

theorem expJ_transport_expansion {d : Nat}
    (J : Sym2 (Site d) → ℝ) (beta : ℝ) {n m : Nat}
    (hnm : n ≤ m) (E : Finset (Sym2 (interactionBoxVertices d n)))
    (hEdiag : ∀ e ∈ E, ¬e.IsDiag) :
    expJ (interactionBoxGraph d m).edgeFinset
        (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0)
        (fun s => Real.exp (-weightedEdgeSpinSum beta
          (interactionBoxCoupling J m)
          (interactionBoxTransportedEdges d hnm E) s)) =
      ∑ T ∈ E.powerset,
        weightedEdgeExpansionCoeff beta (interactionBoxCoupling J n) E T *
          expJ (interactionBoxGraph d m).edgeFinset
            (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0)
            (spinProd ((edgeBoundary (E \ T)).map
              (interactionBoxVertexIncl d hnm))) := by
  unfold expJ
  have hnum :
      (∑ s : ConfigSpace (interactionBoxVertices d m),
        Real.exp (-weightedEdgeSpinSum beta (interactionBoxCoupling J m)
          (interactionBoxTransportedEdges d hnm E) s) *
          wJ (interactionBoxGraph d m).edgeFinset
            (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0) s) =
      ∑ T ∈ E.powerset,
        weightedEdgeExpansionCoeff beta (interactionBoxCoupling J n) E T *
          ∑ s : ConfigSpace (interactionBoxVertices d m),
            spinProd ((edgeBoundary (E \ T)).map
              (interactionBoxVertexIncl d hnm)) s *
              wJ (interactionBoxGraph d m).edgeFinset
                (fun e => beta * interactionBoxCoupling J m e)
                (fun _ => 0) s := by
    simp_rw [exp_neg_weightedEdgeSpinSum_transport_expansion
      J beta hnm E hEdiag]
    calc
      (∑ s : ConfigSpace (interactionBoxVertices d m),
        (∑ T ∈ E.powerset,
          weightedEdgeExpansionCoeff beta (interactionBoxCoupling J n) E T *
            spinProd ((edgeBoundary (E \ T)).map
              (interactionBoxVertexIncl d hnm)) s) *
          wJ (interactionBoxGraph d m).edgeFinset
            (fun e => beta * interactionBoxCoupling J m e) (fun _ => 0) s) =
        ∑ s : ConfigSpace (interactionBoxVertices d m),
          ∑ T ∈ E.powerset,
            weightedEdgeExpansionCoeff beta (interactionBoxCoupling J n) E T *
              (spinProd ((edgeBoundary (E \ T)).map
                (interactionBoxVertexIncl d hnm)) s *
                wJ (interactionBoxGraph d m).edgeFinset
                  (fun e => beta * interactionBoxCoupling J m e)
                  (fun _ => 0) s) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro T hT
          ring
      _ = ∑ T ∈ E.powerset,
          ∑ s : ConfigSpace (interactionBoxVertices d m),
            weightedEdgeExpansionCoeff beta (interactionBoxCoupling J n) E T *
              (spinProd ((edgeBoundary (E \ T)).map
                (interactionBoxVertexIncl d hnm)) s *
                wJ (interactionBoxGraph d m).edgeFinset
                  (fun e => beta * interactionBoxCoupling J m e)
                  (fun _ => 0) s) := by
          rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [← Finset.mul_sum]
  rw [hnum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T hT
  ring

theorem cosh_product_transport {d : Nat}
    (J : Sym2 (Site d) → ℝ) (beta : ℝ) {n m : Nat}
    (hnm : n ≤ m) (E : Finset (Sym2 (interactionBoxVertices d n))) :
    (∏ e ∈ interactionBoxTransportedEdges d hnm E,
        Real.cosh (beta * interactionBoxCoupling J m e)) =
      ∏ e ∈ E, Real.cosh (beta * interactionBoxCoupling J n e) := by
  unfold interactionBoxTransportedEdges sym2FinsetMap
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro e he
  change Real.cosh (beta * interactionBoxCoupling J m
    (Sym2.map (interactionBoxVertexIncl d hnm) e)) = _
  rw [interactionBoxCoupling_transport J hnm]

noncomputable def interactionEdgeVertexSupport {d : Nat}
    (F : Finset (Sym2 (Site d))) : Finset (Site d) :=
  F.biUnion Sym2.toFinset

theorem finiteInteractionEdges_subset_box {d : Nat}
    (F : Finset (Sym2 (Site d))) :
    ∃ N, ∀ e ∈ F, ∀ x ∈ e, x ∈ box d N := by
  obtain ⟨N, hN⟩ := finite_subset_box
    (interactionEdgeVertexSupport F : Set (Site d))
    (interactionEdgeVertexSupport F).finite_toSet
  refine ⟨N, ?_⟩
  intro e he x hx
  apply hN
  exact Finset.mem_biUnion.mpr ⟨e, he, by simpa using hx⟩



theorem generalFreeBoxCurrentMeasure_parityAvoid_full_tendsto {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d))) (hFdiag : ∀ e ∈ F, ¬e.IsDiag) :
    ∃ L : ℝ≥0∞, Tendsto
      (fun n => (generalFreeBoxCurrentMeasure J hJ n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityAvoidCylinder F)) atTop (nhds L) := by
  obtain ⟨N, hFN⟩ := finiteInteractionEdges_subset_box F
  let E : Finset (Sym2 (interactionBoxVertices d N)) :=
    interactionBoxLiftedEdges F hFN
  have hE : E ⊆ (interactionBoxGraph d N).edgeFinset :=
    interactionBoxLiftedEdges_subset_edgeFinset F hFN hFdiag
  have hEdiag : ∀ e ∈ E, ¬e.IsDiag := fun e he =>
    (interactionBoxGraph d N).not_isDiag_of_mem_edgeFinset (hE he)
  have hEambient :
      sym2FinsetMap (Function.Embedding.subtype
        (fun x : Site d => x ∈ interactionBoxVertices d N)) E = F :=
    interactionBoxLiftedEdges_ambient_image F hFN
  let c : ℝ := ∏ e ∈ E,
    Real.cosh (beta * interactionBoxCoupling J N e)
  let term (T : Finset (Sym2 (interactionBoxVertices d N))) (k : Nat) : ℝ :=
    expJ (interactionBoxGraph d (k + N)).edgeFinset
      (fun e => beta * interactionBoxCoupling J (k + N) e) (fun _ => 0)
      (spinProd ((edgeBoundary (E \ T)).map
        (interactionBoxVertexIncl d (Nat.le_add_left N k))))
  have hterm (T : Finset (Sym2 (interactionBoxVertices d N))) :
      ∃ L : ℝ, Tendsto (term T) atTop (nhds L) := by
    let A : Finset (Site d) :=
      (edgeBoundary (E \ T)).map (Function.Embedding.subtype
        (fun x : Site d => x ∈ interactionBoxVertices d N))
    obtain ⟨L, hfull⟩ := generalInteractionBox_spinProd_tendsto
      J hJ beta hbeta.le A
    have htail := (tendsto_add_atTop_iff_nat N).2 hfull
    refine ⟨L, ?_⟩
    apply htail.congr'
    filter_upwards [] with k
    unfold term A
    rw [interactionBoxSpinSupport_map_base]
  choose ell hell using hterm
  let r : ℝ := ∑ T ∈ E.powerset,
    weightedEdgeExpansionCoeff beta (interactionBoxCoupling J N) E T * ell T
  have hpoly : Tendsto
      (fun k => ∑ T ∈ E.powerset,
        weightedEdgeExpansionCoeff beta (interactionBoxCoupling J N) E T *
          term T k) atTop (nhds r) := by
    have hs := tendsto_finsetSum E.powerset (fun T hT =>
      (hell T).const_mul
        (weightedEdgeExpansionCoeff beta (interactionBoxCoupling J N) E T))
    simpa only [r] using hs
  have hreal : Tendsto
      (fun k => (∑ T ∈ E.powerset,
        weightedEdgeExpansionCoeff beta (interactionBoxCoupling J N) E T *
          term T k) * c) atTop (nhds (r * c)) :=
    hpoly.mul_const c
  have hofReal := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  refine ⟨ENNReal.ofReal (r * c), (tendsto_add_atTop_iff_nat N).1 ?_⟩
  apply hofReal.congr'
  filter_upwards [] with k
  let hNk : N ≤ k + N := Nat.le_add_left N k
  let Ek : Finset (Sym2 (interactionBoxVertices d (k + N))) :=
    interactionBoxTransportedEdges d hNk E
  have hEk : Ek ⊆ (interactionBoxGraph d (k + N)).edgeFinset :=
    interactionBoxTransportedEdges_subset_edgeFinset d hNk E hE
  have himage :
      sym2FinsetMap (Function.Embedding.subtype
        (fun x : Site d => x ∈ interactionBoxVertices d (k + N))) Ek = F := by
    exact (interactionBoxTransportedEdges_ambient_image d hNk E).trans hEambient
  have hmass := generalFreeBoxCurrentMeasure_parityAvoid_edgeImage
    J hJ beta hbeta Ek hEk
  rw [himage] at hmass
  rw [hmass, expJ_transport_expansion J beta hNk E hEdiag,
    cosh_product_transport J beta hNk E]
  rfl

theorem diagonal_not_mem_range_interactionBoxEdgeIncl
    (d n : Nat) (e : Sym2 (Site d)) (he : e.IsDiag) :
    e ∉ Set.range (interactionBoxEdgeIncl d n) := by
  rintro ⟨f, rfl⟩
  have hsource : ¬f.1.IsDiag :=
    (interactionBoxGraph d n).not_isDiag_of_mem_edgeFinset f.2
  exact hsource ((Sym2.isDiag_map Subtype.val_injective).mp he)

theorem extendInteractionBoxCurrent_diag_zero
    (d n : Nat) (m : EdgeCurrent (interactionBoxGraph d n))
    (e : Sym2 (Site d)) (he : e.IsDiag) :
    extendInteractionBoxCurrent d n m e = 0 := by
  exact extendInteractionBoxCurrent_outside d n m e
    (diagonal_not_mem_range_interactionBoxEdgeIncl d n e he)

def nonDiagonalEdgeFinset {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) : Finset (Sym2 V) :=
  F.filter fun e => ¬e.IsDiag

theorem preimage_currentParityAvoidCylinder_nonDiagonal
    (d n : Nat) (F : Finset (Sym2 (Site d))) :
    extendInteractionBoxCurrent d n ⁻¹' currentParityAvoidCylinder F =
      extendInteractionBoxCurrent d n ⁻¹'
        currentParityAvoidCylinder (nonDiagonalEdgeFinset F) := by
  ext m
  simp only [Set.mem_preimage, currentParityAvoidCylinder,
    nonDiagonalEdgeFinset, Finset.mem_filter]
  constructor
  · intro h e heF
    exact h e heF.1
  · intro h e heF
    by_cases he : e.IsDiag
    · rw [extendInteractionBoxCurrent_diag_zero d n m e he]
      norm_num
    · exact h e ⟨heF, he⟩

theorem generalFreeBoxCurrentMeasure_parityAvoid_nonDiagonal
    {d : Nat} (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 ≤ beta) (n : Nat)
    (F : Finset (Sym2 (Site d))) :
    (generalFreeBoxCurrentMeasure J hJ n beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder F) =
      (generalFreeBoxCurrentMeasure J hJ n beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder (nonDiagonalEdgeFinset F)) := by
  have hmeasF := measurableSet_currentParityAvoidCylinder F
  have hmeasD := measurableSet_currentParityAvoidCylinder
    (nonDiagonalEdgeFinset F)
  change Measure.map (extendInteractionBoxCurrent d n)
      ((sourcelessCurrentPMF (interactionBoxGraph d n) beta
        (interactionBoxCoupling J n) hbeta
          (fun e => hJ (Sym2.map Subtype.val e))).toMeasure)
        (currentParityAvoidCylinder F) =
    Measure.map (extendInteractionBoxCurrent d n)
      ((sourcelessCurrentPMF (interactionBoxGraph d n) beta
        (interactionBoxCoupling J n) hbeta
          (fun e => hJ (Sym2.map Subtype.val e))).toMeasure)
        (currentParityAvoidCylinder (nonDiagonalEdgeFinset F))
  rw [Measure.map_apply (measurable_extendInteractionBoxCurrent d n) hmeasF,
    Measure.map_apply (measurable_extendInteractionBoxCurrent d n) hmeasD,
    preimage_currentParityAvoidCylinder_nonDiagonal]



theorem generalFreeBoxCurrentMeasure_parityAvoid_full_tendsto_all {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d))) :
    ∃ L : ℝ≥0∞, Tendsto
      (fun n => (generalFreeBoxCurrentMeasure J hJ n beta hbeta.le :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))
          (currentParityAvoidCylinder F)) atTop (nhds L) := by
  let D := nonDiagonalEdgeFinset F
  have hDdiag : ∀ e ∈ D, ¬e.IsDiag := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  obtain ⟨L, hL⟩ := generalFreeBoxCurrentMeasure_parityAvoid_full_tendsto
    J hJ beta hbeta D hDdiag
  refine ⟨L, hL.congr' ?_⟩
  filter_upwards [] with n
  exact (generalFreeBoxCurrentMeasure_parityAvoid_nonDiagonal
    J hJ beta hbeta.le n F).symm

end StatMech.FrontierB
