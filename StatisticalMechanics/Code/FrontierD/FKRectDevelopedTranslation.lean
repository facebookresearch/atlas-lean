/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectColumnTranslation
import Code.FrontierD.FKRectDevelopedWideCrossing



open Set

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section



theorem fkRectCriticalEventMass_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s) (q : Real)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass R q A =
      fkRectCriticalEventMass R q
        ((fkRectEvenRowTranslationConfigurationEquiv R s) '' A) := by
  classical
  let C := fkRectEvenRowTranslationConfigurationEquiv R s
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta : R.Configuration =>
    (C '' A).indicator
      (fun eta => fkRectCriticalRandomClusterProb R q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hmem : C omega ∈ C '' A ↔ omega ∈ A := by
    constructor
    · rintro ⟨eta, heta, heq⟩
      exact C.injective heq ▸ heta
    · intro homega
      exact ⟨omega, homega, rfl⟩
  have hprob := fkRectCriticalRandomClusterProb_evenRowTranslation
    R s hs q omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hmem.mpr hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (fun h => hA (hmem.mp h))]

theorem fkRectTorusGraph_adj_columnTranslation
    (R : FKRectTorus) (s : Int) (x y : R.Vertex) :
    (fkRectTorusGraph R).Adj
        (fkRectColumnTranslationVertexEquiv R s x)
        (fkRectColumnTranslationVertexEquiv R s y) ↔
      (fkRectTorusGraph R).Adj x y := by
  constructor
  · rintro ⟨a, ha⟩
    let b := (fkRectColumnTranslationEdgeEquiv R s).symm a
    refine ⟨b, ?_⟩
    have ht := fkRectTorusIndexedEdge_columnTranslation R s b
    rw [(fkRectColumnTranslationEdgeEquiv R s).apply_symm_apply a, ha] at ht
    apply Sym2.map.injective
      (fkRectColumnTranslationVertexEquiv R s).injective
    simpa only [Sym2.map_mk] using ht.symm
  · rintro ⟨a, ha⟩
    refine ⟨fkRectColumnTranslationEdgeEquiv R s a, ?_⟩
    rw [fkRectTorusIndexedEdge_columnTranslation R s, ha, Sym2.map_mk]



theorem fkRectFullGraphConfiguration_columnTranslation
    (R : FKRectTorus) (s : Int) (omega : R.Configuration)
    (e : Sym2 R.Vertex) :
    fkRectFullGraphConfiguration R
        (fkRectColumnTranslationConfigurationEquiv R s omega)
        (Sym2.map (fkRectColumnTranslationVertexEquiv R s) e) =
      fkRectFullGraphConfiguration R omega e := by
  classical
  by_cases he : e ∈ (fkRectTorusGraph R).edgeSet
  · obtain ⟨a, ha⟩ := (mem_fkRectTorusGraph_edgeSet_iff R e).1 he
    rw [← ha, ← fkRectTorusIndexedEdge_columnTranslation,
      fkRectFullGraphConfiguration_indexedEdge,
      fkRectFullGraphConfiguration_indexedEdge]
    change omega ((fkRectColumnTranslationEdgeEquiv R s).symm
      (fkRectColumnTranslationEdgeEquiv R s a)) = omega a
    rw [(fkRectColumnTranslationEdgeEquiv R s).symm_apply_apply]
  · have htranslate :
        Sym2.map (fkRectColumnTranslationVertexEquiv R s) e ∉
          (fkRectTorusGraph R).edgeSet := by
      intro ht
      induction e using Sym2.ind with
      | _ x y =>
        simp only [Sym2.map_mk] at ht
        rw [SimpleGraph.mem_edgeSet] at ht
        apply he
        rw [SimpleGraph.mem_edgeSet]
        exact (fkRectTorusGraph_adj_columnTranslation R s x y).mp ht
    rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R _ htranslate,
      fkRectFullGraphConfiguration_eq_false_of_not_edge R _ he]



theorem fkRectFullGraphConfiguration_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s)
    (omega : R.Configuration) (e : Sym2 R.Vertex) :
    fkRectFullGraphConfiguration R
        (fkRectEvenRowTranslationConfigurationEquiv R s omega)
        (Sym2.map (fkRectEvenRowTranslationVertexEquiv R s) e) =
      fkRectFullGraphConfiguration R omega e := by
  classical
  by_cases he : e ∈ (fkRectTorusGraph R).edgeSet
  · obtain ⟨a, ha⟩ := (mem_fkRectTorusGraph_edgeSet_iff R e).1 he
    rw [← ha, ← fkRectTorusIndexedEdge_evenRowTranslation R s hs,
      fkRectFullGraphConfiguration_indexedEdge,
      fkRectFullGraphConfiguration_indexedEdge]
    change omega ((fkRectEvenRowTranslationEdgeEquiv R s).symm
      (fkRectEvenRowTranslationEdgeEquiv R s a)) = omega a
    rw [(fkRectEvenRowTranslationEdgeEquiv R s).symm_apply_apply]
  · have htranslate :
        Sym2.map (fkRectEvenRowTranslationVertexEquiv R s) e ∉
          (fkRectTorusGraph R).edgeSet := by
      intro ht
      induction e using Sym2.ind with
      | _ x y =>
        simp only [Sym2.map_mk] at ht
        rw [SimpleGraph.mem_edgeSet] at ht
        apply he
        rw [SimpleGraph.mem_edgeSet]
        exact (fkRectTorusGraph_adj_evenRowTranslation
          R s hs x y).mp ht
    rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R _ htranslate,
      fkRectFullGraphConfiguration_eq_false_of_not_edge R _ he]


def fkRectDevelopedSiteTranslate (u : Int × Int) (z : Site 2) : Site 2 :=
  ![z 0 + u.1, z 1 + u.2]

@[simp] theorem fkRectDevelopedSiteTranslate_apply_zero
    (u : Int × Int) (z : Site 2) :
    fkRectDevelopedSiteTranslate u z 0 = z 0 + u.1 := by
  simp [fkRectDevelopedSiteTranslate]

@[simp] theorem fkRectDevelopedSiteTranslate_apply_one
    (u : Int × Int) (z : Site 2) :
    fkRectDevelopedSiteTranslate u z 1 = z 1 + u.2 := by
  simp [fkRectDevelopedSiteTranslate]



theorem fkRectSquareUndevelopPoint_add_checkerboardTranslation
    (z : Int × Int) (c t : Int) :
    fkRectSquareUndevelopPoint (z + (c + t, c - t)) =
      fkRectSquareUndevelopPoint z + (c, 2 * t) := by
  apply Prod.ext <;>
    simp [fkRectSquareUndevelopPoint] <;> omega

theorem fkRectIntModFin_add
    {N : Nat} (hN : 0 < N) (z s : Int) :
    fkRectIntModFin hN
        (((fkRectIntModFin hN z).val : Int) + s) =
      fkRectIntModFin hN (z + s) := by
  apply Fin.ext
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ N).mp
    rw [fkRectIntModFin_cast, fkRectIntModFin_cast]
    push_cast
    rw [fkRectIntModFin_cast]
  · exact (fkRectIntModFin hN
      (((fkRectIntModFin hN z).val : Int) + s)).isLt
  · exact (fkRectIntModFin hN (z + s)).isLt

theorem fkRectColumnTranslation_squareRepresentativeVertex
    (R : FKRectTorus) (c : Int) (z : Int × Int) :
    fkRectColumnTranslationVertexEquiv R c
        (fkRectSquareRepresentativeVertex R z) =
      fkRectSquareRepresentativeVertex R (z + (c, c)) := by
  apply Prod.ext
  · change fkRectColumnTranslate R c
        (fkRectIntModFin R.width_pos
          (z.2 + (z.1 - z.2) / 2)) =
      fkRectIntModFin R.width_pos
        (z.2 + c + (z.1 + c - (z.2 + c)) / 2)
    unfold fkRectColumnTranslate
    rw [fkRectIntModFin_add]
    congr 1
    ring
  · apply Fin.ext
    simp [fkRectColumnTranslationVertexEquiv_apply,
      fkRectSquareRepresentativeVertex,
      fkRectSquareUndevelopPoint]

theorem fkRectEvenRowTranslation_squareRepresentativeVertex
    (R : FKRectTorus) (t : Nat) : Even (2 * t) →
    ∀ z : Int × Int,
      fkRectEvenRowTranslationVertexEquiv R (2 * t)
          (fkRectSquareRepresentativeVertex R z) =
        fkRectSquareRepresentativeVertex R
          (z + ((t : Int), -(t : Int))) := by
  intro _ z
  apply Prod.ext
  · apply Fin.ext
    simp [fkRectEvenRowTranslationVertexEquiv_apply,
      fkRectSquareRepresentativeVertex,
      fkRectSquareUndevelopPoint]
    congr 1
    omega
  · change fkRectRowTranslate R (2 * t)
        (fkRectIntModFin R.height_pos (z.1 - z.2)) =
      fkRectIntModFin R.height_pos
        (z.1 + t - (z.2 + -(t : Int)))
    unfold fkRectRowTranslate
    rw [fkRectIntModFin_add]
    congr 1
    push_cast
    ring




def fkRectCheckerboardTranslationVertexEquiv
    (R : FKRectTorus) (c : Int) (t : Nat) : R.Vertex ≃ R.Vertex :=
  (fkRectEvenRowTranslationVertexEquiv R (2 * t)).trans
    (fkRectColumnTranslationVertexEquiv R c)

def fkRectCheckerboardTranslationConfigurationEquiv
    (R : FKRectTorus) (c : Int) (t : Nat) :
    R.Configuration ≃ R.Configuration :=
  (fkRectEvenRowTranslationConfigurationEquiv R (2 * t)).trans
    (fkRectColumnTranslationConfigurationEquiv R c)

@[simp] theorem fkRectCheckerboardTranslationVertexEquiv_apply
    (R : FKRectTorus) (c : Int) (t : Nat) (v : R.Vertex) :
    fkRectCheckerboardTranslationVertexEquiv R c t v =
      fkRectColumnTranslationVertexEquiv R c
        (fkRectEvenRowTranslationVertexEquiv R (2 * t) v) := rfl

@[simp] theorem fkRectCheckerboardTranslationConfigurationEquiv_apply
    (R : FKRectTorus) (c : Int) (t : Nat) (omega : R.Configuration) :
    fkRectCheckerboardTranslationConfigurationEquiv R c t omega =
      fkRectColumnTranslationConfigurationEquiv R c
        (fkRectEvenRowTranslationConfigurationEquiv R (2 * t) omega) := rfl

theorem fkRectCheckerboardTranslation_squareRepresentativeVertex
    (R : FKRectTorus) (c : Int) (t : Nat) (z : Int × Int) :
    fkRectCheckerboardTranslationVertexEquiv R c t
        (fkRectSquareRepresentativeVertex R z) =
      fkRectSquareRepresentativeVertex R
        (z + (c + t, c - t)) := by
  calc
    _ = fkRectColumnTranslationVertexEquiv R c
          (fkRectSquareRepresentativeVertex R
            (z + ((t : Int), -(t : Int)))) := by
      rw [fkRectCheckerboardTranslationVertexEquiv_apply,
        fkRectEvenRowTranslation_squareRepresentativeVertex R t
          (even_two_mul t) z]
    _ = fkRectSquareRepresentativeVertex R
          ((z + ((t : Int), -(t : Int))) + (c, c)) :=
      fkRectColumnTranslation_squareRepresentativeVertex R c _
    _ = _ := by
      congr 1
      apply Prod.ext <;> simp <;> ring

theorem fkRectFullGraphConfiguration_checkerboardTranslation
    (R : FKRectTorus) (c : Int) (t : Nat)
    (omega : R.Configuration) (e : Sym2 R.Vertex) :
    fkRectFullGraphConfiguration R
        (fkRectCheckerboardTranslationConfigurationEquiv R c t omega)
        (Sym2.map (fkRectCheckerboardTranslationVertexEquiv R c t) e) =
      fkRectFullGraphConfiguration R omega e := by
  rw [show Sym2.map (fkRectCheckerboardTranslationVertexEquiv R c t) e =
      Sym2.map (fkRectColumnTranslationVertexEquiv R c)
        (Sym2.map (fkRectEvenRowTranslationVertexEquiv R (2 * t)) e) by
    rw [Sym2.map_map]
    rfl]
  rw [fkRectCheckerboardTranslationConfigurationEquiv_apply,
    fkRectFullGraphConfiguration_columnTranslation,
    fkRectFullGraphConfiguration_evenRowTranslation
      R (2 * t) (even_two_mul t)]

theorem fkRectCriticalRandomClusterProb_checkerboardTranslation
    (R : FKRectTorus) (c : Int) (t : Nat) (q : Real)
    (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb R q
        (fkRectCheckerboardTranslationConfigurationEquiv R c t omega) =
      fkRectCriticalRandomClusterProb R q omega := by
  rw [fkRectCheckerboardTranslationConfigurationEquiv_apply,
    fkRectCriticalRandomClusterProb_columnTranslation,
    fkRectCriticalRandomClusterProb_evenRowTranslation
      R (2 * t) (even_two_mul t)]

theorem fkRectCriticalEventMass_checkerboardTranslation
    (R : FKRectTorus) (c : Int) (t : Nat) (q : Real)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass R q A =
      fkRectCriticalEventMass R q
        ((fkRectCheckerboardTranslationConfigurationEquiv R c t) '' A) := by
  classical
  let C := fkRectCheckerboardTranslationConfigurationEquiv R c t
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta : R.Configuration =>
    (C '' A).indicator
      (fun eta => fkRectCriticalRandomClusterProb R q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hmem : C omega ∈ C '' A ↔ omega ∈ A := by
    constructor
    · rintro ⟨eta, heta, heq⟩
      exact C.injective heq ▸ heta
    · intro homega
      exact ⟨omega, homega, rfl⟩
  have hprob := fkRectCriticalRandomClusterProb_checkerboardTranslation
    R c t q omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hmem.mpr hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (fun h => hA (hmem.mp h))]

theorem fkRectCheckerboardTranslation_developedSquareVertex
    (R : FKRectTorus) (n : Nat) (c : Int) (t : Nat) (z : Site 2) :
    fkRectCheckerboardTranslationVertexEquiv R c t
        (fkRectDevelopedSquareVertex R n z) =
      fkRectDevelopedSquareVertex R n
        (fkRectDevelopedSiteTranslate (c + t, c - t) z) := by
  rw [fkRectDevelopedSquareVertex,
    fkRectCheckerboardTranslation_squareRepresentativeVertex]
  congr 2
  apply Prod.ext <;>
    simp [fkRectDevelopedSquarePoint, fkRectDevelopedSiteTranslate] <;> ring

theorem fkRectDevelopedSquarePullback_checkerboardTranslation
    (R : FKRectTorus) (n : Nat) (c : Int) (t : Nat)
    (omega : R.Configuration) (e : Sym2 (Site 2)) :
    fkRectDevelopedSquarePullback R n
        (fkRectCheckerboardTranslationConfigurationEquiv R c t omega)
        (Sym2.map
          (fkRectDevelopedSiteTranslate (c + t, c - t)) e) =
      fkRectDevelopedSquarePullback R n omega e := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Sym2.map_mk]
    unfold fkRectDevelopedSquarePullback
    simp only [Sym2.map_mk]
    rw [← fkRectCheckerboardTranslation_developedSquareVertex,
      ← fkRectCheckerboardTranslation_developedSquareVertex]
    rw [show s(
        fkRectCheckerboardTranslationVertexEquiv R c t
          (fkRectDevelopedSquareVertex R n x),
        fkRectCheckerboardTranslationVertexEquiv R c t
          (fkRectDevelopedSquareVertex R n y)) =
      Sym2.map (fkRectCheckerboardTranslationVertexEquiv R c t)
        s(fkRectDevelopedSquareVertex R n x,
          fkRectDevelopedSquareVertex R n y) by
      simp only [Sym2.map_mk]]
    exact fkRectFullGraphConfiguration_checkerboardTranslation R c t omega _

theorem fkRectDevelopedSquarePullback_translateConfig_checkerboardTranslation
    (R : FKRectTorus) (n : Nat) (c : Int) (t : Nat)
    (omega : R.Configuration) :
    StatMech.Universality.translateConfig
        (![c + t, c - t] : Site 2)
        (fkRectDevelopedSquarePullback R n
          (fkRectCheckerboardTranslationConfigurationEquiv R c t omega)) =
      fkRectDevelopedSquarePullback R n omega := by
  funext e
  rw [StatMech.Universality.translateConfig]
  simpa [fkRectDevelopedSiteTranslate,
    StatMech.FK.PeriodicPlanar.siteTranslate] using
      (fkRectDevelopedSquarePullback_checkerboardTranslation
        R n c t omega e)

theorem fkRectCheckerboardTranslation_mem_horizontalCrossing
    (R : FKRectTorus) (n : Nat) (c : Int) (t : Nat)
    (a b d e : Int) (omega : R.Configuration)
    (hcross : omega ∈ fkRectDevelopedRectangleHorizontalCrossingEvent
      R n a b d e) :
    fkRectCheckerboardTranslationConfigurationEquiv R c t omega ∈
      fkRectDevelopedRectangleHorizontalCrossingEvent R n
        (a + (c + t)) (b + (c + t))
        (d + (c - t)) (e + (c - t)) := by
  let u : Site 2 := ![c + t, c - t]
  let sigma := fkRectDevelopedSquarePullback R n
    (fkRectCheckerboardTranslationConfigurationEquiv R c t omega)
  have hconfig : StatMech.Universality.translateConfig u sigma =
      fkRectDevelopedSquarePullback R n omega := by
    simpa [u, sigma] using
      (fkRectDevelopedSquarePullback_translateConfig_checkerboardTranslation
        R n c t omega)
  have hbase : HorizontalCrossing
      (StatMech.Universality.translateConfig u sigma) a b d e := by
    rw [hconfig]
    exact hcross
  have hshift := StatMech.Universality.cti_horizontalCrossing_translate_fwd
    a b d e u sigma hbase
  simpa [fkRectDevelopedRectangleHorizontalCrossingEvent, u, sigma] using hshift

theorem fkRectCheckerboardTranslation_mem_verticalCrossing
    (R : FKRectTorus) (n : Nat) (c : Int) (t : Nat)
    (a b d e : Int) (omega : R.Configuration)
    (hcross : omega ∈ fkRectDevelopedRectangleVerticalCrossingEvent
      R n a b d e) :
    fkRectCheckerboardTranslationConfigurationEquiv R c t omega ∈
      fkRectDevelopedRectangleVerticalCrossingEvent R n
        (a + (c + t)) (b + (c + t))
        (d + (c - t)) (e + (c - t)) := by
  let u : Site 2 := ![c + t, c - t]
  let sigma := fkRectDevelopedSquarePullback R n
    (fkRectCheckerboardTranslationConfigurationEquiv R c t omega)
  have hconfig : StatMech.Universality.translateConfig u sigma =
      fkRectDevelopedSquarePullback R n omega := by
    simpa [u, sigma] using
      (fkRectDevelopedSquarePullback_translateConfig_checkerboardTranslation
        R n c t omega)
  have hbase : VerticalCrossing
      (StatMech.Universality.translateConfig u sigma) a b d e := by
    rw [hconfig]
    exact hcross
  have hshift := StatMech.Universality.cti_verticalCrossing_translate_fwd
    a b d e u sigma hbase
  simpa [fkRectDevelopedRectangleVerticalCrossingEvent, u, sigma] using hshift

theorem fkRectCritical_horizontalCrossingMass_le_checkerboardTranslate
    (R : FKRectTorus) (n : Nat) (c : Int) (t : Nat)
    {q : Real} (hq : 0 < q) (a b d e : Int) :
    fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent R n a b d e) ≤
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleHorizontalCrossingEvent R n
          (a + (c + t)) (b + (c + t))
          (d + (c - t)) (e + (c - t))) := by
  let C := fkRectCheckerboardTranslationConfigurationEquiv R c t
  calc
    _ = fkRectCriticalEventMass R q
        (C '' fkRectDevelopedRectangleHorizontalCrossingEvent
          R n a b d e) :=
      fkRectCriticalEventMass_checkerboardTranslation R c t q _
    _ ≤ _ := fkRectCriticalEventMass_mono R hq (by
      rintro eta ⟨omega, homega, rfl⟩
      exact fkRectCheckerboardTranslation_mem_horizontalCrossing
        R n c t a b d e omega homega)

theorem fkRectCritical_verticalCrossingMass_le_checkerboardTranslate
    (R : FKRectTorus) (n : Nat) (c : Int) (t : Nat)
    {q : Real} (hq : 0 < q) (a b d e : Int) :
    fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleVerticalCrossingEvent R n a b d e) ≤
      fkRectCriticalEventMass R q
        (fkRectDevelopedRectangleVerticalCrossingEvent R n
          (a + (c + t)) (b + (c + t))
          (d + (c - t)) (e + (c - t))) := by
  let C := fkRectCheckerboardTranslationConfigurationEquiv R c t
  calc
    _ = fkRectCriticalEventMass R q
        (C '' fkRectDevelopedRectangleVerticalCrossingEvent
          R n a b d e) :=
      fkRectCriticalEventMass_checkerboardTranslation R c t q _
    _ ≤ _ := fkRectCriticalEventMass_mono R hq (by
      rintro eta ⟨omega, homega, rfl⟩
      exact fkRectCheckerboardTranslation_mem_verticalCrossing
        R n c t a b d e omega homega)



theorem fkRectCritical_developedSquareHorizontalMass_ge_evenTranslate
    (R : FKRectTorus) (n shift : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q
      (fkRectDevelopedRectangleHorizontalCrossingEvent R n
        (2 * shift) (2 * shift + n) 0 n) := by
  have hseed := fkRectCritical_developedSquareHorizontalMass_ge
    R n hn hwidth hheight hq
  have htranslate :=
    fkRectCritical_horizontalCrossingMass_le_checkerboardTranslate
      R n (shift : Int) shift (zero_lt_one.trans_le hq) 0 n 0 n
  have hseed' : 1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q
      (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 n 0 n) := by
    simpa only [fkRectDevelopedSquareHorizontalCrossingEvent,
      fkRectDevelopedRectangleHorizontalCrossingEvent] using hseed
  apply hseed'.trans
  convert htranslate using 1 <;> push_cast <;> ring

theorem fkRectCritical_developedSquareVerticalMass_ge_evenTranslate
    (R : FKRectTorus) (n shift : Nat) (hn : 1 ≤ n)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    {q : Real} (hq : 1 ≤ q) :
    1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q
      (fkRectDevelopedRectangleVerticalCrossingEvent R n
        (2 * shift) (2 * shift + n) 0 n) := by
  have hseed := fkRectCritical_developedSquareVerticalMass_ge
    R n hn hwidth hheight hq
  have htranslate :=
    fkRectCritical_verticalCrossingMass_le_checkerboardTranslate
      R n (shift : Int) shift (zero_lt_one.trans_le hq) 0 n 0 n
  have hseed' : 1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q
      (fkRectDevelopedRectangleVerticalCrossingEvent R n 0 n 0 n) := by
    simpa only [fkRectDevelopedSquareVerticalCrossingEvent,
      fkRectDevelopedRectangleVerticalCrossingEvent] using hseed
  apply hseed'.trans
  convert htranslate using 1 <;> push_cast <;> ring

end

end StatMech.FrontierD
