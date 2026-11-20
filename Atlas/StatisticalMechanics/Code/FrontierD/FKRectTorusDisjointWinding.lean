/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectTorusSquareCoverIntersection









open SimpleGraph

namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section


def FKRectDartListUsesPoint {L : Nat} (l : List (ons_Dart L))
    (p : ZMod L × ZMod L) : Prop :=
  ∃ d ∈ l, d.1 = p ∨ ons_dirStep L d.2 d.1 = p

namespace FKRectDartListUsesPoint

variable {L : Nat}

theorem of_mem {l : List (ons_Dart L)} {d : ons_Dart L}
    (hd : d ∈ l) :
    FKRectDartListUsesPoint l d.1 :=
  ⟨d, hd, Or.inl rfl⟩

theorem of_mem_end {l : List (ons_Dart L)} {d : ons_Dart L}
    (hd : d ∈ l) :
    FKRectDartListUsesPoint l (ons_dirStep L d.2 d.1) :=
  ⟨d, hd, Or.inr rfl⟩

private theorem exists_ne_zero_of_sum_ne_zero
    (f : ons_Dart L → Int) {l : List (ons_Dart L)}
    (h : (l.map f).sum ≠ 0) :
    ∃ d ∈ l, f d ≠ 0 := by
  contrapose! h
  exact List.sum_eq_zero (fun z hz => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hz
    exact h d hd)

theorem of_horizontal_ne_zero {l : List (ons_Dart L)}
    {p : ZMod L × ZMod L}
    (h : (l.map (fun d => IntegralSquareTorusCycle.dartHorizontal d p)).sum
      ≠ 0) :
    FKRectDartListUsesPoint l p := by
  obtain ⟨d, hd, hne⟩ := exists_ne_zero_of_sum_ne_zero
    (fun d => IntegralSquareTorusCycle.dartHorizontal d p) h
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · have hp : (x, y) = p := by
      have hp' : p = (x, y) := by
        simpa [IntegralSquareTorusCycle.dartHorizontal,
          IntegralSquareTorusCycle.pointMass] using hne
      exact hp'.symm
    exact ⟨((x, y), 0), hd, Or.inl hp⟩
  · simp [IntegralSquareTorusCycle.dartHorizontal] at hne
  · have hp : (x - 1, y) = p := by
      have hp' : p = (x - 1, y) := by
        simpa [IntegralSquareTorusCycle.dartHorizontal,
          IntegralSquareTorusCycle.pointMass] using hne
      exact hp'.symm
    refine ⟨((x, y), 2), hd, Or.inr ?_⟩
    simpa [ons_dirStep] using hp
  · simp [IntegralSquareTorusCycle.dartHorizontal] at hne

theorem of_vertical_ne_zero {l : List (ons_Dart L)}
    {p : ZMod L × ZMod L}
    (h : (l.map (fun d => IntegralSquareTorusCycle.dartVertical d p)).sum
      ≠ 0) :
    FKRectDartListUsesPoint l p := by
  obtain ⟨d, hd, hne⟩ := exists_ne_zero_of_sum_ne_zero
    (fun d => IntegralSquareTorusCycle.dartVertical d p) h
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · simp [IntegralSquareTorusCycle.dartVertical] at hne
  · have hp : (x, y) = p := by
      have hp' : p = (x, y) := by
        simpa [IntegralSquareTorusCycle.dartVertical,
          IntegralSquareTorusCycle.pointMass] using hne
      exact hp'.symm
    exact ⟨((x, y), 1), hd, Or.inl hp⟩
  · simp [IntegralSquareTorusCycle.dartVertical] at hne
  · have hp : (x, y - 1) = p := by
      have hp' : p = (x, y - 1) := by
        simpa [IntegralSquareTorusCycle.dartVertical,
          IntegralSquareTorusCycle.pointMass] using hne
      exact hp'.symm
    refine ⟨((x, y), 3), hd, Or.inr ?_⟩
    simpa [ons_dirStep] using hp

theorem of_horizontal_ne_zero_east {l : List (ons_Dart L)}
    {p : ZMod L × ZMod L}
    (h : (l.map (fun d => IntegralSquareTorusCycle.dartHorizontal d p)).sum
      ≠ 0) :
    FKRectDartListUsesPoint l (p.1 + 1, p.2) := by
  obtain ⟨d, hd, hne⟩ := exists_ne_zero_of_sum_ne_zero
    (fun d => IntegralSquareTorusCycle.dartHorizontal d p) h
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · have hp : p = (x, y) := by
      simpa [IntegralSquareTorusCycle.dartHorizontal,
        IntegralSquareTorusCycle.pointMass] using hne
    refine ⟨((x, y), 0), hd, Or.inr ?_⟩
    rw [hp]
    simp [ons_dirStep]
  · simp [IntegralSquareTorusCycle.dartHorizontal] at hne
  · have hp : p = (x - 1, y) := by
      simpa [IntegralSquareTorusCycle.dartHorizontal,
        IntegralSquareTorusCycle.pointMass] using hne
    refine ⟨((x, y), 2), hd, Or.inl ?_⟩
    rw [hp]
    apply Prod.ext <;> simp
  · simp [IntegralSquareTorusCycle.dartHorizontal] at hne

theorem of_vertical_ne_zero_north {l : List (ons_Dart L)}
    {p : ZMod L × ZMod L}
    (h : (l.map (fun d => IntegralSquareTorusCycle.dartVertical d p)).sum
      ≠ 0) :
    FKRectDartListUsesPoint l (p.1, p.2 + 1) := by
  obtain ⟨d, hd, hne⟩ := exists_ne_zero_of_sum_ne_zero
    (fun d => IntegralSquareTorusCycle.dartVertical d p) h
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · simp [IntegralSquareTorusCycle.dartVertical] at hne
  · have hp : p = (x, y) := by
      simpa [IntegralSquareTorusCycle.dartVertical,
        IntegralSquareTorusCycle.pointMass] using hne
    refine ⟨((x, y), 1), hd, Or.inr ?_⟩
    rw [hp]
    simp [ons_dirStep]
  · simp [IntegralSquareTorusCycle.dartVertical] at hne
  · have hp : p = (x, y - 1) := by
      simpa [IntegralSquareTorusCycle.dartVertical,
        IntegralSquareTorusCycle.pointMass] using hne
    refine ⟨((x, y), 3), hd, Or.inl ?_⟩
    rw [hp]
    apply Prod.ext <;> simp

end FKRectDartListUsesPoint


theorem IntegralSquareTorusCycle.ofDartList_locallyDisjoint
    {L : Nat} [Fact (2 < L)]
    (v w : List (ons_Dart L))
    (hv : IntegralSquareTorusCycle.DartListBalanced v)
    (hw : IntegralSquareTorusCycle.DartListBalanced w)
    (hdisj : ∀ p, FKRectDartListUsesPoint v p →
      ¬ FKRectDartListUsesPoint w p) :
    (IntegralSquareTorusCycle.ofDartList v hv).LocallyDisjoint
      (IntegralSquareTorusCycle.ofDartList w hw) := by
  intro p
  by_cases hC :
      (IntegralSquareTorusCycle.ofDartList v hv).horizontal p = 0 ∧
        (IntegralSquareTorusCycle.ofDartList v hv).vertical p = 0
  · exact Or.inl hC
  · right
    constructor
    · by_contra hwest
      have hCuses : FKRectDartListUsesPoint v p := by
        rcases not_and_or.mp hC with hh | hh
        · exact FKRectDartListUsesPoint.of_horizontal_ne_zero hh
        · exact FKRectDartListUsesPoint.of_vertical_ne_zero hh
      have hWuses : FKRectDartListUsesPoint w p := by
        have h := FKRectDartListUsesPoint.of_horizontal_ne_zero_east
          (l := w) hwest
        simpa using h
      exact hdisj p hCuses hWuses
    · by_contra hsouth
      have hCuses : FKRectDartListUsesPoint v p := by
        rcases not_and_or.mp hC with hh | hh
        · exact FKRectDartListUsesPoint.of_horizontal_ne_zero hh
        · exact FKRectDartListUsesPoint.of_vertical_ne_zero hh
      have hWuses : FKRectDartListUsesPoint w p := by
        have h := FKRectDartListUsesPoint.of_vertical_ne_zero_north
          (l := w) hsouth
        simpa using h
      exact hdisj p hCuses hWuses



theorem fkRectSquareRepresentativeVertex_eq_of_pointMod_eq
    (R : FKRectTorus) {a b : Int × Int}
    (hmod : fkRectIntegralSquarePointMod (fkRectSquareCoverSide R) a =
      fkRectIntegralSquarePointMod (fkRectSquareCoverSide R) b) :
    fkRectSquareRepresentativeVertex R a =
      fkRectSquareRepresentativeVertex R b := by
  let L := fkRectSquareCoverSide R
  have hxcast : (a.1 : ZMod L) = (b.1 : ZMod L) := by
    exact congrArg Prod.fst hmod
  have hycast : (a.2 : ZMod L) = (b.2 : ZMod L) := by
    exact congrArg Prod.snd hmod
  have hxdiv : (L : Int) ∣ b.1 - a.1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub a.1 b.1 L).mp hxcast
  have hydiv : (L : Int) ∣ b.2 - a.2 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub a.2 b.2 L).mp hycast
  obtain ⟨A, hA⟩ := hxdiv
  obtain ⟨B, hB⟩ := hydiv
  let alpha : Int := -A
  let beta : Int := -B
  let u : Int × Int :=
    ((R.height / 2 : Nat) * (alpha + beta),
      (R.width : Int) * (alpha - beta))
  have hheight : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    exact_mod_cast Nat.two_mul_div_two_of_even R.height_even
  have hLcast : (L : Int) = (R.width : Int) * R.height := by
    simp [L, fkRectSquareCoverSide]
  have hA' : a.1 - b.1 =
      (R.width : Int) * R.height * (-A) := by
    calc
      a.1 - b.1 = -(b.1 - a.1) := by ring
      _ = -((L : Int) * A) := by rw [hA]
      _ = (R.width : Int) * R.height * (-A) := by
        rw [hLcast]
        ring
  have hB' : a.2 - b.2 =
      (R.width : Int) * R.height * (-B) := by
    calc
      a.2 - b.2 = -(b.2 - a.2) := by ring
      _ = -((L : Int) * B) := by rw [hB]
      _ = (R.width : Int) * R.height * (-B) := by
        rw [hLcast]
        ring
  have hdeck : fkRectSquareDeckTranslation R u = a - b := by
    apply Prod.ext
    · simp only [fkRectSquareDeckTranslation, u,
        Prod.fst_sub, alpha, beta]
      calc
        (R.width : Int) * ((R.height / 2 : Nat) * (-A + -B)) +
              (R.height / 2 : Nat) * ((R.width : Int) * (-A - -B)) =
            (R.width : Int) * R.height * (-A) := by
              rw [← hheight]
              ring
        _ = a.1 - b.1 := hA'.symm
    · simp only [fkRectSquareDeckTranslation, u,
        Prod.snd_sub, alpha, beta]
      calc
        (R.width : Int) * ((R.height / 2 : Nat) * (-A + -B)) -
              (R.height / 2 : Nat) * ((R.width : Int) * (-A - -B)) =
            (R.width : Int) * R.height * (-B) := by
              rw [← hheight]
              ring
        _ = a.2 - b.2 := hB'.symm
  apply fkRectVertexSquareClass_injective R
  rw [fkRectVertexSquareClass_representative,
    fkRectVertexSquareClass_representative]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  exact (mem_fkRectSquareDeckLattice_iff R _).mpr ⟨u, hdeck⟩



theorem fkRectSquareRepresentativeVertex_add_deck
    (R : FKRectTorus) (z u : Int × Int) :
    fkRectSquareRepresentativeVertex R
        (z + fkRectSquareDeckTranslation R u) =
      fkRectSquareRepresentativeVertex R z := by
  apply fkRectVertexSquareClass_injective R
  rw [fkRectVertexSquareClass_representative,
    fkRectVertexSquareClass_representative]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply (mem_fkRectSquareDeckLattice_iff R _).mpr
  refine ⟨u, ?_⟩
  apply Prod.ext <;> simp




theorem FKRectSquareWalkLift.exists_supportedIntegralDartPath
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    ∃ l : List FKRectIntegralSquareDart,
      FKRectIntegralSquareDartPath
        (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q) l ∧
      ∀ d ∈ l,
        fkRectSquareRepresentativeVertex R d.1 ∈ w.support ∧
        fkRectSquareRepresentativeVertex R
          (fkRectIntegralSquareDartEnd d) ∈ w.support := by
  induction h with
  | nil p hp =>
      exact ⟨[], FKRectIntegralSquareDartPath.nil _, by simp⟩
  | @cons x y z hxy w p q r hp hq hdisp haxis tail ih =>
      obtain ⟨l, hl, hsupp⟩ := ih
      obtain ⟨mu, hmu⟩ := haxis.exists_direction
      refine ⟨(fkRectSquareDevelopPoint p, mu) :: l,
        FKRectIntegralSquareDartPath.cons _ hmu hl, ?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · constructor
        · rw [fkRectSquareRepresentativeVertex_developPoint, hp]
          simp
        · rw [hmu, fkRectSquareRepresentativeVertex_developPoint, hq]
          simp
      · obtain ⟨hstart, hend⟩ := hsupp d hd
        constructor
        · rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem x hstart
        · rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem x hend


def FKRectIntegralDartListSupportedOn (R : FKRectTorus)
    (l : List FKRectIntegralSquareDart) (S : R.Vertex → Prop) : Prop :=
  ∀ d ∈ l,
    S (fkRectSquareRepresentativeVertex R d.1) ∧
      S (fkRectSquareRepresentativeVertex R
        (fkRectIntegralSquareDartEnd d))

theorem fkRectNatScale_squareDeckTranslation
    (R : FKRectTorus) (n : Nat) (u : Int × Int) :
    fkRectNatScale n (fkRectSquareDeckTranslation R u) =
      fkRectSquareDeckTranslation R
        ((n : Int) * u.1, (n : Int) * u.2) := by
  apply Prod.ext <;>
    simp [fkRectNatScale, fkRectSquareDeckTranslation] <;> ring

theorem fkRectSquareRepresentativeVertex_dartTranslate_deck
    (R : FKRectTorus) (u : Int × Int)
    (d : FKRectIntegralSquareDart) :
    fkRectSquareRepresentativeVertex R
        (fkRectIntegralSquareDartTranslate
          (fkRectSquareDeckTranslation R u) d).1 =
      fkRectSquareRepresentativeVertex R d.1 := by
  exact fkRectSquareRepresentativeVertex_add_deck R d.1 u

theorem fkRectSquareRepresentativeVertex_dartTranslateEnd_deck
    (R : FKRectTorus) (u : Int × Int)
    (d : FKRectIntegralSquareDart) :
    fkRectSquareRepresentativeVertex R
        (fkRectIntegralSquareDartEnd
          (fkRectIntegralSquareDartTranslate
            (fkRectSquareDeckTranslation R u) d)) =
      fkRectSquareRepresentativeVertex R
        (fkRectIntegralSquareDartEnd d) := by
  rw [fkRectIntegralSquareDartEnd_translate]
  convert fkRectSquareRepresentativeVertex_add_deck R
    (fkRectIntegralSquareDartEnd d) u using 1



theorem FKRectIntegralDartListSupportedOn.repeatTranslated_deck
    (R : FKRectTorus) {l : List FKRectIntegralSquareDart}
    {S : R.Vertex → Prop} (u : Int × Int)
    (h : FKRectIntegralDartListSupportedOn R l S) (n : Nat) :
    FKRectIntegralDartListSupportedOn R
      (fkRectRepeatTranslatedDartPath l
        (fkRectSquareDeckTranslation R u) n) S := by
  induction n with
  | zero =>
      simp [FKRectIntegralDartListSupportedOn,
        fkRectRepeatTranslatedDartPath]
  | succ n ih =>
      intro d hd
      rw [fkRectRepeatTranslatedDartPath, List.mem_append] at hd
      rcases hd with hd | hd
      · exact ih d hd
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
        rw [fkRectNatScale_squareDeckTranslation]
        constructor
        · rw [fkRectSquareRepresentativeVertex_dartTranslate_deck]
          exact (h a ha).1
        · rw [fkRectSquareRepresentativeVertex_dartTranslateEnd_deck]
          exact (h a ha).2



theorem FKRectIntegralDartListSupportedOn.exists_pointLift
    (R : FKRectTorus) {l : List FKRectIntegralSquareDart}
    {S : R.Vertex → Prop}
    (h : FKRectIntegralDartListSupportedOn R l S)
    {p : ZMod (fkRectSquareCoverSide R) ×
      ZMod (fkRectSquareCoverSide R)}
    (hp : FKRectDartListUsesPoint
      (l.map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide R))) p) :
    ∃ z : Int × Int,
      fkRectIntegralSquarePointMod (fkRectSquareCoverSide R) z = p ∧
      S (fkRectSquareRepresentativeVertex R z) := by
  obtain ⟨dmod, hdmod, hstart | hend⟩ := hp
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hdmod
    exact ⟨d.1, hstart, (h d hd).1⟩
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hdmod
    refine ⟨fkRectIntegralSquareDartEnd d, ?_, (h d hd).2⟩
    rw [fkRectIntegralSquareDartMod_end] at hend
    exact hend



theorem fkRectDartListUsesPoint_disjoint_of_supported
    (R : FKRectTorus) {l k : List FKRectIntegralSquareDart}
    {S T : R.Vertex → Prop}
    (hl : FKRectIntegralDartListSupportedOn R l S)
    (hk : FKRectIntegralDartListSupportedOn R k T)
    (hST : ∀ x, S x → ¬ T x) :
    ∀ p,
      FKRectDartListUsesPoint
          (l.map (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide R))) p →
        ¬ FKRectDartListUsesPoint
          (k.map (fkRectIntegralSquareDartMod
            (fkRectSquareCoverSide R))) p := by
  intro p hp hq
  obtain ⟨a, ha, hSa⟩ := hl.exists_pointLift R hp
  obtain ⟨b, hb, hTb⟩ := hk.exists_pointLift R hq
  have hab : fkRectSquareRepresentativeVertex R a =
      fkRectSquareRepresentativeVertex R b := by
    apply fkRectSquareRepresentativeVertex_eq_of_pointMod_eq R
    rw [ha, hb]
  exact hST _ hSa (hab ▸ hTb)



def fkRectSquareCoverPointVertex (R : FKRectTorus)
    (p : ZMod (fkRectSquareCoverSide R) ×
      ZMod (fkRectSquareCoverSide R)) : R.Vertex :=
  fkRectSquareRepresentativeVertex R
    ((p.1.val : Int), (p.2.val : Int))

theorem fkRectSquareCoverPointVertex_eq_of_pointMod
    (R : FKRectTorus) (z : Int × Int)
    (p : ZMod (fkRectSquareCoverSide R) ×
      ZMod (fkRectSquareCoverSide R))
    (h : fkRectIntegralSquarePointMod (fkRectSquareCoverSide R) z = p) :
    fkRectSquareRepresentativeVertex R z =
      fkRectSquareCoverPointVertex R p := by
  apply fkRectSquareRepresentativeVertex_eq_of_pointMod_eq R
  rw [h]
  apply Prod.ext <;>
    simp [fkRectIntegralSquarePointMod]


structure FKRectSquareCoverDartWitness (R : FKRectTorus)
    (u : Int × Int) where
  darts : List (ons_Dart (fkRectSquareCoverSide R))
  balanced : IntegralSquareTorusCycle.DartListBalanced darts
  xWrap_eq : (darts.map ons_xWrapSign).sum = u.1
  yWrap_eq : (darts.map ons_yWrapSign).sum = u.2



theorem FKRectIntegralSquareDartPath.exists_squareCoverDartWitness
    (R : FKRectTorus) {p u : Int × Int}
    {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p
      (p.1 + u.1, p.2 + u.2) l) :
    ∃ C : FKRectSquareCoverDartWitness R u,
      C.darts =
        (fkRectRepeatTranslatedDartPath l u
          (fkRectSquareCoverSide R)).map
            (fkRectIntegralSquareDartMod (fkRectSquareCoverSide R)) := by
  let L := fkRectSquareCoverSide R
  letI : Fact (2 < L) := ⟨fkRectSquareCoverSide_gt_two R⟩
  let repeated := fkRectRepeatTranslatedDartPath l u L
  have hrepeated : FKRectIntegralSquareDartPath p
      (p.1 + (L : Int) * u.1, p.2 + (L : Int) * u.2) repeated :=
    h.repeatTranslated L
  have hpointMod : fkRectIntegralSquarePointMod L p =
      fkRectIntegralSquarePointMod L
        (p.1 + (L : Int) * u.1, p.2 + (L : Int) * u.2) := by
    apply Prod.ext <;> simp [fkRectIntegralSquarePointMod]
  let darts := repeated.map (fkRectIntegralSquareDartMod L)
  have hbalanced : IntegralSquareTorusCycle.DartListBalanced darts :=
    hrepeated.dartListBalanced_of_pointMod_eq L hpointMod
  have hxEquation := hrepeated.displacement_x_eq_wrap (L := L)
  have hyEquation := hrepeated.displacement_y_eq_wrap (L := L)
  rw [hpointMod] at hxEquation hyEquation
  simp only [sub_self, zero_add] at hxEquation hyEquation
  rw [add_sub_cancel_left] at hxEquation hyEquation
  have hL : (L : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans (by norm_num : 0 < 2)
      (fkRectSquareCoverSide_gt_two R)))
  have hxWrap : (darts.map ons_xWrapSign).sum = u.1 := by
    apply mul_left_cancel₀ hL
    exact hxEquation.symm
  have hyWrap : (darts.map ons_yWrapSign).sum = u.2 := by
    apply mul_left_cancel₀ hL
    exact hyEquation.symm
  refine ⟨⟨darts, hbalanced, hxWrap, hyWrap⟩, ?_⟩
  rfl

theorem FKRectSquareCoverDartWitness.not_independent_of_disjointSupport
    {R : FKRectTorus} {u v : Int × Int}
    (C : FKRectSquareCoverDartWitness R u)
    (D : FKRectSquareCoverDartWitness R v)
    (hdisj : ∀ p, FKRectDartListUsesPoint C.darts p →
      ¬ FKRectDartListUsesPoint D.darts p) :
    ¬ FKRectWindingIndependent u v := by
  intro hind
  apply hind
  have hlocal := IntegralSquareTorusCycle.ofDartList_locallyDisjoint
    C.darts D.darts C.balanced D.balanced hdisj
  have hdet :=
    IntegralSquareTorusCycle.dartList_winding_det_eq_zero_of_locallyDisjoint
      C.darts C.balanced D.darts D.balanced hlocal
  rw [C.xWrap_eq, C.yWrap_eq, D.xWrap_eq, D.yWrap_eq] at hdet
  exact hdet



theorem FKRectSquareWalkLift.not_windingIndependent_of_support_disjoint
    (R : FKRectTorus)
    {G H : SimpleGraph R.Vertex} {x y : R.Vertex}
    {w : G.Walk x x} {z : H.Walk y y}
    {p q a b : Int × Int}
    (hw : FKRectSquareWalkLift R w p q)
    (hz : FKRectSquareWalkLift R z a b)
    (hdisj : ∀ v, v ∈ w.support → v ∈ z.support → False) :
    ¬ FKRectWindingIndependent
      (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
  obtain ⟨l, hl, hlsupp⟩ := hw.exists_supportedIntegralDartPath R
  obtain ⟨k, hk, hksupp⟩ := hz.exists_supportedIntegralDartPath R
  let u := fkRectSquareDeckTranslation R (fkRectWalkWinding R w)
  let v := fkRectSquareDeckTranslation R (fkRectWalkWinding R z)
  have hwu := hw.closed_develop_sub_eq_deck_winding R
  have hzv := hz.closed_develop_sub_eq_deck_winding R
  have hq : fkRectSquareDevelopPoint q =
      ((fkRectSquareDevelopPoint p).1 + u.1,
        (fkRectSquareDevelopPoint p).2 + u.2) := by
    dsimp [u]
    apply Prod.ext
    · have h := congrArg Prod.fst hwu
      simp only [Prod.fst_sub] at h ⊢
      omega
    · have h := congrArg Prod.snd hwu
      simp only [Prod.snd_sub] at h ⊢
      omega
  have hb : fkRectSquareDevelopPoint b =
      ((fkRectSquareDevelopPoint a).1 + v.1,
        (fkRectSquareDevelopPoint a).2 + v.2) := by
    dsimp [v]
    apply Prod.ext
    · have h := congrArg Prod.fst hzv
      simp only [Prod.fst_sub] at h ⊢
      omega
    · have h := congrArg Prod.snd hzv
      simp only [Prod.snd_sub] at h ⊢
      omega
  rw [hq] at hl
  rw [hb] at hk
  obtain ⟨C, hC⟩ := hl.exists_squareCoverDartWitness R
  obtain ⟨D, hD⟩ := hk.exists_squareCoverDartWitness R
  have hls : FKRectIntegralDartListSupportedOn R l
      (fun t => t ∈ w.support) := hlsupp
  have hks : FKRectIntegralDartListSupportedOn R k
      (fun t => t ∈ z.support) := hksupp
  have hlrepeat := hls.repeatTranslated_deck R
    (fkRectWalkWinding R w) (fkRectSquareCoverSide R)
  have hkrepeat := hks.repeatTranslated_deck R
    (fkRectWalkWinding R z) (fkRectSquareCoverSide R)
  have hcoverDisjoint : ∀ t, FKRectDartListUsesPoint C.darts t →
      ¬ FKRectDartListUsesPoint D.darts t := by
    rw [hC, hD]
    exact fkRectDartListUsesPoint_disjoint_of_supported
      R hlrepeat hkrepeat (fun t ht hs => hdisj t ht hs)
  intro hind
  apply C.not_independent_of_disjointSupport D hcoverDisjoint
  exact (fkRectWindingIndependent_squareDeck_iff R _ _).mpr hind



theorem fkRectClosedWalks_not_windingIndependent_of_support_disjoint
    (R : FKRectTorus)
    {G H : SimpleGraph R.Vertex} (hG : G ≤ fkRectTorusGraph R)
    (hH : H ≤ fkRectTorusGraph R)
    {x y : R.Vertex} (w : G.Walk x x) (z : H.Walk y y)
    (hdisj : ∀ v, v ∈ w.support → v ∈ z.support → False) :
    ¬ FKRectWindingIndependent
      (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
  let p : Int × Int := ((x.1.val : Int), (x.2.val : Int))
  let a : Int × Int := ((y.1.val : Int), (y.2.val : Int))
  have hp : fkRectLiftedVertex R p = x := by
    apply Prod.ext <;> simp [p, fkRectLiftedVertex]
  have ha : fkRectLiftedVertex R a = y := by
    apply Prod.ext <;> simp [a, fkRectLiftedVertex]
  obtain ⟨q, hw⟩ := fkRectWalk_exists_squareLift R hG w p hp
  obtain ⟨b, hz⟩ := fkRectWalk_exists_squareLift R hH z a ha
  exact hw.not_windingIndependent_of_support_disjoint R hz hdisj



theorem fkRectClosedWalks_not_windingIndependent_of_not_reachable
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex}
    (hxy : ¬ (fkRectOpenGraph R omega).Reachable x y)
    (w : (fkRectOpenGraph R omega).Walk x x)
    (z : (fkRectOpenGraph R omega).Walk y y) :
    ¬ FKRectWindingIndependent
      (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
  apply fkRectClosedWalks_not_windingIndependent_of_support_disjoint R
    (fkRectOpenGraph_le_torusGraph R omega)
    (fkRectOpenGraph_le_torusGraph R omega) w z
  intro v hvw hvz
  have hxv : (fkRectOpenGraph R omega).Reachable x v :=
    (w.takeUntil v hvw).reachable
  have hyv : (fkRectOpenGraph R omega).Reachable y v :=
    (z.takeUntil v hvz).reachable
  exact hxy (hxv.trans hyv.symm)



theorem fkRectClosedWindingSubgroup_cross_dependent
    (R : FKRectTorus) (omega : R.Configuration)
    {x y : R.Vertex}
    (hxy : ¬ (fkRectOpenGraph R omega).Reachable x y) :
    ∀ u ∈ fkRectClosedWindingSubgroup R omega x,
      ∀ v ∈ fkRectClosedWindingSubgroup R omega y,
        ¬ FKRectWindingIndependent u v := by
  rintro u ⟨w, rfl⟩ v ⟨z, rfl⟩
  exact fkRectClosedWalks_not_windingIndependent_of_not_reachable
    R omega hxy w z



theorem not_windingIndependent_add_of_pairwise
    (a b c d : Int × Int)
    (hab : ¬ FKRectWindingIndependent a b)
    (had : ¬ FKRectWindingIndependent a d)
    (hbc : ¬ FKRectWindingIndependent b c)
    (hcd : ¬ FKRectWindingIndependent c d) :
    ¬ FKRectWindingIndependent (a + c) (b + d) := by
  unfold FKRectWindingIndependent at hab had hbc hcd ⊢
  simp only [not_ne_iff, Prod.fst_add, Prod.snd_add] at *
  linear_combination hab + had - hbc + hcd



theorem windingSubgroup_sup_not_rankTwo_of_pairwise_dependent
    (H K : AddSubgroup (Int × Int))
    (hH : ∀ a ∈ H, ∀ b ∈ H, ¬ FKRectWindingIndependent a b)
    (hK : ∀ a ∈ K, ∀ b ∈ K, ¬ FKRectWindingIndependent a b)
    (hHK : ∀ a ∈ H, ∀ b ∈ K, ¬ FKRectWindingIndependent a b) :
    ¬ ∃ a ∈ H ⊔ K, ∃ b ∈ H ⊔ K,
      FKRectWindingIndependent a b := by
  rintro ⟨a, ha, b, hb, hind⟩
  rw [AddSubgroup.mem_sup] at ha hb
  obtain ⟨x, hx, y, hy, rfl⟩ := ha
  obtain ⟨z, hz, t, ht, rfl⟩ := hb
  exact (not_windingIndependent_add_of_pairwise x z y t
    (hH x hx z hz) (hHK x hx t ht)
    (hHK z hz y hy) (hK y hy t ht)) hind

end

end StatMech.FrontierD
