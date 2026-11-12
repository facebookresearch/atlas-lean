/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDevelopedWideCrossing
import Code.FK.TranslationInvariance



open Set SimpleGraph StatMech.Lattice

namespace StatMech.FrontierD

noncomputable section


def fkRectRowReflection (R : FKRectTorus) (center : Nat)
    (y : Fin R.height) : Fin R.height :=
  ⟨(2 * center + R.height - y.val) % R.height,
    Nat.mod_lt _ R.height_pos⟩

@[simp] theorem fkRectRowReflection_val (R : FKRectTorus) (center : Nat)
    (y : Fin R.height) :
    (fkRectRowReflection R center y).val =
      (2 * center + R.height - y.val) % R.height :=
  rfl

theorem fkRectRowReflection_involutive (R : FKRectTorus) (center : Nat) :
    Function.Involutive (fkRectRowReflection R center) := by
  intro y
  apply Fin.ext
  let A := 2 * center + R.height
  let r := (A - y.val) % R.height
  have hyA : y.val <= A := by
    dsimp [A]
    omega
  have hrH : r < R.height := Nat.mod_lt _ R.height_pos
  have hrA : r <= A := by
    dsimp [A]
    omega
  have hmod : r ≡ A - y.val [MOD R.height] :=
    Nat.mod_modEq (A - y.val) R.height
  have hsub : A - r ≡ A - (A - y.val) [MOD R.height] :=
    Nat.ModEq.sub hrA (Nat.sub_le A y.val) (Nat.ModEq.refl A) hmod
  have hAy : A - (A - y.val) = y.val := Nat.sub_sub_self hyA
  change (A - r) % R.height = y.val
  rw [Nat.mod_eq_of_modEq (hAy ▸ hsub) y.isLt]

@[simp] theorem fkRectRowReflection_twice (R : FKRectTorus) (center : Nat)
    (y : Fin R.height) :
    fkRectRowReflection R center (fkRectRowReflection R center y) = y :=
  fkRectRowReflection_involutive R center y


def fkRectRowReflectionEquiv (R : FKRectTorus) (center : Nat) :
    Fin R.height ≃ Fin R.height where
  toFun := fkRectRowReflection R center
  invFun := fkRectRowReflection R center
  left_inv := fkRectRowReflection_involutive R center
  right_inv := fkRectRowReflection_involutive R center

theorem fkRectRowReflection_even_iff (R : FKRectTorus) (center : Nat)
    (y : Fin R.height) :
    Even (fkRectRowReflection R center y).val ↔ Even y.val := by
  rw [fkRectRowReflection_val, Even.mod_even_iff R.height_even,
    Nat.even_sub (by omega)]
  have hA : Even (2 * center + R.height) :=
    (even_two_mul center).add R.height_even
  simp [hA]

theorem fkRectRowReflection_cast (R : FKRectTorus) (center : Nat)
    (y : Fin R.height) :
    ((fkRectRowReflection R center y).val : ZMod R.height) =
      (2 * center : ZMod R.height) - y.val := by
  simp [fkRectRowReflection]
  rw [Nat.cast_sub (by omega : y.val <= 2 * center + R.height)]
  simp

theorem fkRectIntModFin_cast {N : Nat} (hN : 0 < N) (z : Int) :
    ((fkRectIntModFin hN z).val : ZMod N) = z := by
  simp only [fkRectIntModFin, Fin.val_mk]
  have hN0 : (N : Int) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hnonneg : 0 <= z % (N : Int) := Int.emod_nonneg z hN0
  have hzmod : ((z.natMod N : Nat) : Int) = z % (N : Int) := by
    simp [Int.natMod, Int.natCast_toNat_eq_self.mpr hnonneg]
  calc
    ((z.natMod N : Nat) : ZMod N) =
        (((z.natMod N : Nat) : Int) : ZMod N) := by norm_num
    _ = ((z % (N : Int) : Int) : ZMod N) := by rw [hzmod]
    _ = (z : ZMod N) := by simp

theorem fkRectRowReflection_intModFin (R : FKRectTorus) (center : Nat)
    (z : Int) :
    fkRectRowReflection R center (fkRectIntModFin R.height_pos z) =
      fkRectIntModFin R.height_pos (2 * (center : Int) - z) := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ R.height).mp
    calc
      ((fkRectRowReflection R center
          (fkRectIntModFin R.height_pos z)).val : ZMod R.height) =
          (2 * center : ZMod R.height) -
            (fkRectIntModFin R.height_pos z).val :=
        fkRectRowReflection_cast R center _
      _ = (2 * (center : Int) - z : Int) := by
        rw [fkRectIntModFin_cast]
        push_cast
        rfl
      _ = ((fkRectIntModFin R.height_pos
          (2 * (center : Int) - z)).val : ZMod R.height) := by
        rw [fkRectIntModFin_cast]
  · exact (fkRectRowReflection R center
      (fkRectIntModFin R.height_pos z)).isLt
  · exact (fkRectIntModFin R.height_pos
      (2 * (center : Int) - z)).isLt

theorem fkRectRowReflection_cyclicPred (R : FKRectTorus) (center : Nat)
    (y : Fin R.height) :
    fkRectRowReflection R center
        (SixVertexArrows.cyclicPred R.height_pos y) =
      finitePeriodicSucc R.height_pos (fkRectRowReflection R center y) := by
  have hH := R.height_pos
  apply Fin.ext
  simp only [fkRectRowReflection, fkRectCyclicPred_val,
    finitePeriodicSucc, Fin.val_mk]
  split <;> rename_i hzero
  · have hy0 : y.val = 0 := hzero
    simp only [hy0, Nat.sub_zero]
    rw [Nat.mod_add_mod]
    rw [show 2 * center + R.height - (R.height - 1) =
        2 * center + 1 by omega]
    rw [show 2 * center + R.height + 1 =
        (2 * center + 1) + R.height by omega,
      Nat.add_mod_right]
  · have hypos : 0 < y.val := Nat.pos_of_ne_zero hzero
    rw [Nat.mod_add_mod]
    congr 1
    omega

theorem fkRectRowReflection_succ_cyclicPred (R : FKRectTorus)
    (center : Nat) (y : Fin R.height) :
    SixVertexArrows.cyclicPred R.height_pos
        (finitePeriodicSucc R.height_pos
          (fkRectRowReflection R center y)) =
      fkRectRowReflection R center y := by
  have h := finitePeriodicSucc_cyclicPred R.height_pos
    (finitePeriodicSucc R.height_pos (fkRectRowReflection R center y))
  apply (svFinitePeriodicSuccEquiv R.height_pos).injective
  simpa using h


def fkRectDevelopedReflectionVertexEquiv (R : FKRectTorus) (center : Nat) :
    R.Vertex ≃ R.Vertex :=
  (Equiv.refl (Fin R.width)).prodCongr
    (fkRectRowReflectionEquiv R center)

@[simp] theorem fkRectDevelopedReflectionVertexEquiv_apply
    (R : FKRectTorus) (center : Nat) (v : R.Vertex) :
    fkRectDevelopedReflectionVertexEquiv R center v =
      (v.1, fkRectRowReflection R center v.2) :=
  rfl

theorem fkRectSquareUndevelopPoint_developedSwap
    (n : Nat) (z : Site 2) :
    fkRectSquareUndevelopPoint
        (fkRectDevelopedSquarePoint n (StatMech.Universality.crf_swap z)) =
      let p := fkRectSquareUndevelopPoint (fkRectDevelopedSquarePoint n z)
      (p.1, 2 * (n : Int) - p.2) := by
  apply Prod.ext <;>
    simp [fkRectSquareUndevelopPoint, fkRectDevelopedSquarePoint,
      StatMech.Universality.crf_swap, StatMech.Universality.crf_swapFun] <;>
    omega


theorem fkRectDevelopedReflectionVertex_developedSquareVertex
    (R : FKRectTorus) (n : Nat) (z : Site 2) :
    fkRectDevelopedReflectionVertexEquiv R n
        (fkRectDevelopedSquareVertex R n z) =
      fkRectDevelopedSquareVertex R n
        (StatMech.Universality.crf_swap z) := by
  have hrepr (p : Int × Int) :
      fkRectSquareRepresentativeVertex R p =
        fkRectLiftedVertex R (fkRectSquareUndevelopPoint p) := by
    rw [← fkRectSquareRepresentativeVertex_developPoint]
    rw [fkRectSquareDevelopPoint_undevelopPoint]
  rw [fkRectDevelopedSquareVertex, fkRectDevelopedSquareVertex,
    hrepr, hrepr, fkRectDevelopedReflectionVertexEquiv_apply,
    fkRectSquareUndevelopPoint_developedSwap]
  apply Prod.ext
  · rfl
  · exact fkRectRowReflection_intModFin R n _



def fkRectDevelopedReflectionEdgeEquiv (R : FKRectTorus) (center : Nat) :
    R.EdgeIndex ≃ R.EdgeIndex :=
  (Equiv.refl Bool).prodCongr
    ((Equiv.refl (Fin R.width)).prodCongr
      ((fkRectRowReflectionEquiv R center).trans
        (svFinitePeriodicSuccEquiv R.height_pos)))

@[simp] theorem fkRectDevelopedReflectionEdgeEquiv_apply
    (R : FKRectTorus) (center : Nat) (a : R.EdgeIndex) :
    fkRectDevelopedReflectionEdgeEquiv R center a =
      (a.1, (a.2.1, finitePeriodicSucc R.height_pos
        (fkRectRowReflection R center a.2.2))) :=
  rfl



theorem fkRectTorusIndexedEdge_developedReflection
    (R : FKRectTorus) (center : Nat) (a : R.EdgeIndex) :
    fkRectTorusIndexedEdge R
        (fkRectDevelopedReflectionEdgeEquiv R center a) =
      Sym2.map (fkRectDevelopedReflectionVertexEquiv R center)
        (fkRectTorusIndexedEdge R a) := by
  rcases a with ⟨b, x, y⟩
  cases b
  · have hrefEven :
        Even (fkRectRowReflection R center y).val ↔ Even y.val :=
      fkRectRowReflection_even_iff R center y
    have hsuccEven :
        Even (finitePeriodicSucc R.height_pos
          (fkRectRowReflection R center y)).val ↔ ¬ Even y.val := by
      rw [even_finitePeriodicSucc_iff, hrefEven]
    by_cases hy : Even y.val
    · have hsy : ¬ Even (finitePeriodicSucc R.height_pos
          (fkRectRowReflection R center y)).val := by
        simpa [hsuccEven] using hy
      simp only [fkRectDevelopedReflectionEdgeEquiv_apply,
        fkRectTorusIndexedEdge, Bool.false_eq_true, if_false, hy, if_true,
        hsy, fkRectDevelopedReflectionVertexEquiv_apply, Sym2.map_pair_eq]
      rw [fkRectRowReflection_cyclicPred,
        fkRectRowReflection_succ_cyclicPred]
      exact Sym2.eq_swap
    · have hsy : Even (finitePeriodicSucc R.height_pos
          (fkRectRowReflection R center y)).val := hsuccEven.mpr hy
      simp only [fkRectDevelopedReflectionEdgeEquiv_apply,
        fkRectTorusIndexedEdge, Bool.false_eq_true, if_false, hy,
        hsy, if_true, fkRectDevelopedReflectionVertexEquiv_apply,
        Sym2.map_pair_eq]
      rw [fkRectRowReflection_cyclicPred,
        fkRectRowReflection_succ_cyclicPred]
      exact Sym2.eq_swap
  · simp only [fkRectDevelopedReflectionEdgeEquiv_apply,
      fkRectTorusIndexedEdge, if_true,
      fkRectDevelopedReflectionVertexEquiv_apply, Sym2.map_pair_eq]
    rw [fkRectRowReflection_cyclicPred,
      fkRectRowReflection_succ_cyclicPred]
    exact Sym2.eq_swap



theorem fkRectTorusGraph_adj_developedReflection
    (R : FKRectTorus) (center : Nat) (x y : R.Vertex) :
    (fkRectTorusGraph R).Adj
        (fkRectDevelopedReflectionVertexEquiv R center x)
        (fkRectDevelopedReflectionVertexEquiv R center y) ↔
      (fkRectTorusGraph R).Adj x y := by
  constructor
  · rintro ⟨a, ha⟩
    let b := (fkRectDevelopedReflectionEdgeEquiv R center).symm a
    refine ⟨b, ?_⟩
    have href := fkRectTorusIndexedEdge_developedReflection R center b
    rw [(fkRectDevelopedReflectionEdgeEquiv R center).apply_symm_apply a,
      ha] at href
    have hcomp :
        (fkRectDevelopedReflectionVertexEquiv R center) ∘
            (fkRectDevelopedReflectionVertexEquiv R center) = id := by
      funext v
      apply Prod.ext
      · rfl
      · exact fkRectRowReflection_involutive R center v.2
    have := congrArg
      (Sym2.map (fkRectDevelopedReflectionVertexEquiv R center)) href
    rw [Sym2.map_map, hcomp] at this
    have hxinv : fkRectDevelopedReflectionVertexEquiv R center
        (fkRectDevelopedReflectionVertexEquiv R center x) = x :=
      congrFun hcomp x
    have hyinv : fkRectDevelopedReflectionVertexEquiv R center
        (fkRectDevelopedReflectionVertexEquiv R center y) = y :=
      congrFun hcomp y
    rw [Sym2.map_mk, hxinv, hyinv] at this
    simpa using this.symm
  · rintro ⟨a, ha⟩
    refine ⟨fkRectDevelopedReflectionEdgeEquiv R center a, ?_⟩
    rw [fkRectTorusIndexedEdge_developedReflection, ha]
    rfl

theorem fkRectDevelopedReflectionVertexEquiv_symm_apply
    (R : FKRectTorus) (center : Nat) (v : R.Vertex) :
    (fkRectDevelopedReflectionVertexEquiv R center).symm v =
      fkRectDevelopedReflectionVertexEquiv R center v := by
  apply (fkRectDevelopedReflectionVertexEquiv R center).injective
  rw [(fkRectDevelopedReflectionVertexEquiv R center).apply_symm_apply]
  apply Prod.ext
  · rfl
  · exact (fkRectRowReflection_involutive R center v.2).symm

theorem fkRectDevelopedReflectionEdgeEquiv_involutive
    (R : FKRectTorus) (center : Nat) :
    Function.Involutive (fkRectDevelopedReflectionEdgeEquiv R center) := by
  intro a
  apply fkRectTorusIndexedEdge_injective R
  rw [fkRectTorusIndexedEdge_developedReflection,
    fkRectTorusIndexedEdge_developedReflection, Sym2.map_map]
  have hcomp :
      (fkRectDevelopedReflectionVertexEquiv R center) ∘
          (fkRectDevelopedReflectionVertexEquiv R center) = id := by
    funext v
    apply Prod.ext
    · rfl
    · exact fkRectRowReflection_involutive R center v.2
  rw [hcomp]
  simp

@[simp] theorem fkRectDevelopedReflectionEdgeEquiv_twice
    (R : FKRectTorus) (center : Nat) (a : R.EdgeIndex) :
    fkRectDevelopedReflectionEdgeEquiv R center
        (fkRectDevelopedReflectionEdgeEquiv R center a) = a :=
  fkRectDevelopedReflectionEdgeEquiv_involutive R center a

@[simp] theorem fkRectDevelopedReflectionEdgeEquiv_symm_apply
    (R : FKRectTorus) (center : Nat) (a : R.EdgeIndex) :
    (fkRectDevelopedReflectionEdgeEquiv R center).symm a =
      fkRectDevelopedReflectionEdgeEquiv R center a := by
  apply (fkRectDevelopedReflectionEdgeEquiv R center).injective
  rw [(fkRectDevelopedReflectionEdgeEquiv R center).apply_symm_apply,
    fkRectDevelopedReflectionEdgeEquiv_involutive R center a]


def fkRectDevelopedReflectionConfigurationEquiv
    (R : FKRectTorus) (center : Nat) :
    R.Configuration ≃ R.Configuration :=
  Equiv.arrowCongr (fkRectDevelopedReflectionEdgeEquiv R center)
    (Equiv.refl Bool)

@[simp] theorem fkRectDevelopedReflectionConfigurationEquiv_apply
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration)
    (a : R.EdgeIndex) :
    fkRectDevelopedReflectionConfigurationEquiv R center omega a =
      omega ((fkRectDevelopedReflectionEdgeEquiv R center).symm a) :=
  rfl

theorem fkRectOpenGraph_developedReflection_adj
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration)
    (x y : R.Vertex) :
    (fkRectOpenGraph R
      (fkRectDevelopedReflectionConfigurationEquiv R center omega)).Adj
        (fkRectDevelopedReflectionVertexEquiv R center x)
        (fkRectDevelopedReflectionVertexEquiv R center y) ↔
      (fkRectOpenGraph R omega).Adj x y := by
  constructor
  · rintro ⟨a, haopen, ha⟩
    let b := (fkRectDevelopedReflectionEdgeEquiv R center).symm a
    refine ⟨b, ?_, ?_⟩
    · exact haopen
    · have href := fkRectTorusIndexedEdge_developedReflection R center b
      rw [(fkRectDevelopedReflectionEdgeEquiv R center).apply_symm_apply a,
        ha] at href
      have hcomp :
          (fkRectDevelopedReflectionVertexEquiv R center).symm ∘
              (fkRectDevelopedReflectionVertexEquiv R center) = id := by
        exact (fkRectDevelopedReflectionVertexEquiv R center).symm_comp_self
      have := congrArg
        (Sym2.map (fkRectDevelopedReflectionVertexEquiv R center).symm) href
      rw [Sym2.map_map, hcomp] at this
      simpa [Sym2.map_mk,
        fkRectDevelopedReflectionVertexEquiv_symm_apply] using this.symm
  · rintro ⟨b, hbopen, hb⟩
    let a := fkRectDevelopedReflectionEdgeEquiv R center b
    refine ⟨a, ?_, ?_⟩
    · change omega ((fkRectDevelopedReflectionEdgeEquiv R center).symm
          (fkRectDevelopedReflectionEdgeEquiv R center b)) = true
      rw [(fkRectDevelopedReflectionEdgeEquiv R center).symm_apply_apply]
      exact hbopen
    · rw [show a = fkRectDevelopedReflectionEdgeEquiv R center b by rfl,
        fkRectTorusIndexedEdge_developedReflection, hb]
      rfl


def fkRectOpenGraphDevelopedReflectionIso
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration) :
    fkRectOpenGraph R omega ≃g
      fkRectOpenGraph R
        (fkRectDevelopedReflectionConfigurationEquiv R center omega) where
  toEquiv := fkRectDevelopedReflectionVertexEquiv R center
  map_rel_iff' := by
    intro x y
    exact fkRectOpenGraph_developedReflection_adj R center omega x y


theorem fkRectOpenEdgeCount_developedReflection
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration) :
    fkRectOpenEdgeCount R
        (fkRectDevelopedReflectionConfigurationEquiv R center omega) =
      fkRectOpenEdgeCount R omega := by
  unfold fkRectOpenEdgeCount
  let E := fkRectDevelopedReflectionEdgeEquiv R center
  apply Finset.card_bij (fun a _ => E.symm a)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha
  · intro a ha b hb hab
    exact E.symm.injective hab
  · intro b hb
    refine ⟨E b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      change omega (E.symm (E b)) = true
      rw [E.symm_apply_apply]
      exact hb
    · exact E.symm_apply_apply b


theorem fkRectNumClusters_developedReflection
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration) :
    fkRectNumClusters R
        (fkRectDevelopedReflectionConfigurationEquiv R center omega) =
      fkRectNumClusters R omega := by
  unfold fkRectNumClusters
  exact (Fintype.card_congr
    (fkRectOpenGraphDevelopedReflectionIso R center omega).connectedComponentEquiv).symm


theorem fkRectCriticalReducedWeight_developedReflection
    (R : FKRectTorus) (center : Nat) (q : Real)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q
        (fkRectDevelopedReflectionConfigurationEquiv R center omega) =
      fkRectCriticalReducedWeight R q omega := by
  unfold fkRectCriticalReducedWeight
  rw [fkRectOpenEdgeCount_developedReflection,
    fkRectNumClusters_developedReflection]


theorem fkRectCriticalRandomClusterProb_developedReflection
    (R : FKRectTorus) (center : Nat) (q : Real)
    (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb R q
        (fkRectDevelopedReflectionConfigurationEquiv R center omega) =
      fkRectCriticalRandomClusterProb R q omega := by
  unfold fkRectCriticalRandomClusterProb
  rw [fkRectCriticalReducedWeight_developedReflection]



theorem fkRectFullGraphConfiguration_developedReflection
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration)
    (e : Sym2 R.Vertex) :
    fkRectFullGraphConfiguration R
        (fkRectDevelopedReflectionConfigurationEquiv R center omega)
        (Sym2.map (fkRectDevelopedReflectionVertexEquiv R center) e) =
      fkRectFullGraphConfiguration R omega e := by
  classical
  by_cases he : e ∈ (fkRectTorusGraph R).edgeSet
  · obtain ⟨a, ha⟩ := (mem_fkRectTorusGraph_edgeSet_iff R e).1 he
    rw [← ha, ← fkRectTorusIndexedEdge_developedReflection,
      fkRectFullGraphConfiguration_indexedEdge,
      fkRectFullGraphConfiguration_indexedEdge]
    change omega ((fkRectDevelopedReflectionEdgeEquiv R center).symm
      (fkRectDevelopedReflectionEdgeEquiv R center a)) = omega a
    rw [(fkRectDevelopedReflectionEdgeEquiv R center).symm_apply_apply]
  · have href : Sym2.map (fkRectDevelopedReflectionVertexEquiv R center) e ∉
        (fkRectTorusGraph R).edgeSet := by
      intro href
      induction e using Sym2.ind with
      | _ x y =>
        simp only [Sym2.map_mk] at href
        rw [SimpleGraph.mem_edgeSet] at href
        apply he
        rw [SimpleGraph.mem_edgeSet]
        exact (fkRectTorusGraph_adj_developedReflection
          R center x y).mp href
    rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R _ href,
      fkRectFullGraphConfiguration_eq_false_of_not_edge R _ he]



theorem fkRectDevelopedSquarePullback_developedReflection
    (R : FKRectTorus) (n : Nat) (omega : R.Configuration) :
    fkRectDevelopedSquarePullback R n
        (fkRectDevelopedReflectionConfigurationEquiv R n omega) =
      StatMech.Universality.crf_swapConfig
        (fkRectDevelopedSquarePullback R n omega) := by
  funext e
  induction e using Sym2.ind with
  | _ x y =>
    rw [StatMech.Universality.crf_swapConfig_apply]
    change fkRectFullGraphConfiguration R
        (fkRectDevelopedReflectionConfigurationEquiv R n omega)
          (Sym2.map (fkRectDevelopedSquareVertex R n) s(x, y)) =
      fkRectFullGraphConfiguration R omega
        (Sym2.map (fkRectDevelopedSquareVertex R n)
          (Sym2.map StatMech.Universality.crf_swap s(x, y)))
    rw [← fkRectFullGraphConfiguration_developedReflection R n omega
      (Sym2.map (fkRectDevelopedSquareVertex R n)
        (Sym2.map StatMech.Universality.crf_swap s(x, y)))]
    simp only [Sym2.map_mk]
    rw [fkRectDevelopedReflectionVertex_developedSquareVertex,
      fkRectDevelopedReflectionVertex_developedSquareVertex]
    simp only [StatMech.Universality.crf_swap_involutive]



theorem fkRectDevelopedSquare_reflection_mem_vertical_iff
    (R : FKRectTorus) (n : Nat) (omega : R.Configuration) :
    fkRectDevelopedReflectionConfigurationEquiv R n omega ∈
        fkRectDevelopedSquareVerticalCrossingEvent R n ↔
      omega ∈ fkRectDevelopedSquareHorizontalCrossingEvent R n := by
  rw [fkRectDevelopedSquareVerticalCrossingEvent,
    fkRectDevelopedSquareHorizontalCrossingEvent]
  change StatMech.RSW.Box.VerticalCrossing
      (fkRectDevelopedSquarePullback R n
        (fkRectDevelopedReflectionConfigurationEquiv R n omega)) 0 n 0 n ↔
    StatMech.RSW.Box.HorizontalCrossing
      (fkRectDevelopedSquarePullback R n omega) 0 n 0 n
  rw [fkRectDevelopedSquarePullback_developedReflection]
  constructor
  · intro hV
    have hH := StatMech.Universality.crf_vertical_to_horizontal
      0 n 0 n
      (StatMech.Universality.crf_swapConfig
        (fkRectDevelopedSquarePullback R n omega)) hV
    rwa [StatMech.Universality.bat_swapConfig_involutive] at hH
  · intro hH
    exact StatMech.Universality.bat_horizontal_to_vertical_swap
      0 n 0 n (fkRectDevelopedSquarePullback R n omega) hH



theorem fkRectCritical_developedSquareHorizontalMass_eq_verticalMass
    (R : FKRectTorus) (n : Nat) (q : Real) :
    fkRectCriticalEventMass R q
        (fkRectDevelopedSquareHorizontalCrossingEvent R n) =
      fkRectCriticalEventMass R q
        (fkRectDevelopedSquareVerticalCrossingEvent R n) := by
  classical
  let C := fkRectDevelopedReflectionConfigurationEquiv R n
  let H := fkRectDevelopedSquareHorizontalCrossingEvent R n
  let V := fkRectDevelopedSquareVerticalCrossingEvent R n
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta : R.Configuration =>
    V.indicator (fun eta => fkRectCriticalRandomClusterProb R q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega homega
  have hmem : C omega ∈ V ↔ omega ∈ H :=
    fkRectDevelopedSquare_reflection_mem_vertical_iff R n omega
  have hprob : fkRectCriticalRandomClusterProb R q (C omega) =
      fkRectCriticalRandomClusterProb R q omega :=
    fkRectCriticalRandomClusterProb_developedReflection R n q omega
  by_cases hH : omega ∈ H
  · rw [Set.indicator_of_mem hH, Set.indicator_of_mem (hmem.mpr hH), hprob]
  · rw [Set.indicator_of_notMem hH,
      Set.indicator_of_notMem (fun hV => hH (hmem.mp hV))]



theorem fkRectCritical_developedSquareHorizontalMass_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 <= n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 <= q) :
    1 / (2 * (1 + q)) <= fkRectCriticalEventMass R q
      (fkRectDevelopedSquareHorizontalCrossingEvent R n) := by
  rcases fkRectDevelopedSquare_exists_direction_crossing_ge
      R n hn hwidth hheight hq with hH | hV
  · exact hH
  · rwa [fkRectCritical_developedSquareHorizontalMass_eq_verticalMass]


theorem fkRectCritical_developedSquareVerticalMass_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 <= n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 <= q) :
    1 / (2 * (1 + q)) <= fkRectCriticalEventMass R q
      (fkRectDevelopedSquareVerticalCrossingEvent R n) := by
  rw [← fkRectCritical_developedSquareHorizontalMass_eq_verticalMass]
  exact fkRectCritical_developedSquareHorizontalMass_ge
    R n hn hwidth hheight hq




theorem fkRectCritical_developedThreeByOneVerticalMass_ge
    (R : FKRectTorus) (n : Nat) (hn : 1 <= n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 <= q) :
    1 / (2 * (1 + q)) <=
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleVerticalCrossingEvent
          R n 0 (3 * (n : Int)) 0 n) := by
  exact (fkRectCritical_developedSquareVerticalMass_ge
    R n hn hwidth hheight hq).trans
      (fkRectCritical_developedSquareVerticalMass_le_threeByOneVerticalMass
        R n (zero_lt_one.trans_le hq))

end

end StatMech.FrontierD
