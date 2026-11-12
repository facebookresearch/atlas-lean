/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectRefinedDiagonalShearSubdivision










open SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section


def fkRectFaithfulShearPair (p : Int × Int) : Int × Int :=
  (2 * (p.1 + p.2), 2 * (p.1 - p.2))


def fkRectPairSite (p : Int × Int) : Site 2 := ![p.1, p.2]


def fkRectFaithfulShearPoint (p : Int × Int) : Site 2 :=
  fkRectPairSite (fkRectFaithfulShearPair p)

theorem fkRectPairSite_injective : Function.Injective fkRectPairSite := by
  intro p q h
  apply Prod.ext
  · have := congrFun h 0
    simpa [fkRectPairSite] using this
  · have := congrFun h 1
    simpa [fkRectPairSite] using this

theorem fkRectFaithfulShearPair_injective :
    Function.Injective fkRectFaithfulShearPair := by
  rintro ⟨x, y⟩ ⟨a, b⟩ h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp [fkRectFaithfulShearPair] at hx hy
  apply Prod.ext <;> simp <;> omega

theorem fkRectFaithfulShearPoint_injective :
    Function.Injective fkRectFaithfulShearPoint := by
  intro p q h
  apply fkRectFaithfulShearPair_injective
  apply fkRectPairSite_injective
  exact h




def fkRectFaithfulShearDartRoute (d : FKRectIntegralSquareDart) :
    List (Int × Int) :=
  let a := fkRectFaithfulShearPair d.1
  match d.2 with
  | 0 => [a, (a.1 + 1, a.2), (a.1 + 1, a.2 + 1),
      (a.1 + 1, a.2 + 2), (a.1 + 2, a.2 + 2)]
  | 1 => [a, (a.1, a.2 - 1), (a.1 + 1, a.2 - 1),
      (a.1 + 2, a.2 - 1), (a.1 + 2, a.2 - 2)]
  | 2 => [a, (a.1 - 1, a.2), (a.1 - 1, a.2 - 1),
      (a.1 - 1, a.2 - 2), (a.1 - 2, a.2 - 2)]
  | 3 => [a, (a.1, a.2 + 1), (a.1 - 1, a.2 + 1),
      (a.1 - 2, a.2 + 1), (a.1 - 2, a.2 + 2)]



def FKRectIntegralSquareDartsIncident
    (d e : FKRectIntegralSquareDart) : Prop :=
  d.1 = e.1 ∨ d.1 = fkRectIntegralSquareDartEnd e ∨
    fkRectIntegralSquareDartEnd d = e.1 ∨
      fkRectIntegralSquareDartEnd d = fkRectIntegralSquareDartEnd e

private theorem fkRectFaithfulRoutes_incident_from_0
    (x y : Int) (e : FKRectIntegralSquareDart) (r : Int × Int)
    (hr : r ∈ fkRectFaithfulShearDartRoute ((x, y), (0 : Fin 4)))
    (he : r ∈ fkRectFaithfulShearDartRoute e) :
    FKRectIntegralSquareDartsIncident ((x, y), 0) e := by
  rcases e with ⟨⟨a, b⟩, nu⟩
  rcases r with ⟨s, t⟩
  fin_cases nu <;>
    simp [fkRectFaithfulShearDartRoute, fkRectFaithfulShearPair,
      FKRectIntegralSquareDartsIncident,
      fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY, Prod.ext_iff] at hr he ⊢ <;>
    omega

private theorem fkRectFaithfulRoutes_incident_from_1
    (x y : Int) (e : FKRectIntegralSquareDart) (r : Int × Int)
    (hr : r ∈ fkRectFaithfulShearDartRoute ((x, y), (1 : Fin 4)))
    (he : r ∈ fkRectFaithfulShearDartRoute e) :
    FKRectIntegralSquareDartsIncident ((x, y), 1) e := by
  rcases e with ⟨⟨a, b⟩, nu⟩
  rcases r with ⟨s, t⟩
  fin_cases nu <;>
    simp [fkRectFaithfulShearDartRoute, fkRectFaithfulShearPair,
      FKRectIntegralSquareDartsIncident,
      fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY, Prod.ext_iff] at hr he ⊢ <;>
    omega

private theorem fkRectFaithfulRoutes_incident_from_2
    (x y : Int) (e : FKRectIntegralSquareDart) (r : Int × Int)
    (hr : r ∈ fkRectFaithfulShearDartRoute ((x, y), (2 : Fin 4)))
    (he : r ∈ fkRectFaithfulShearDartRoute e) :
    FKRectIntegralSquareDartsIncident ((x, y), 2) e := by
  rcases e with ⟨⟨a, b⟩, nu⟩
  rcases r with ⟨s, t⟩
  fin_cases nu <;>
    simp [fkRectFaithfulShearDartRoute, fkRectFaithfulShearPair,
      FKRectIntegralSquareDartsIncident,
      fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY, Prod.ext_iff] at hr he ⊢ <;>
    omega

private theorem fkRectFaithfulRoutes_incident_from_3
    (x y : Int) (e : FKRectIntegralSquareDart) (r : Int × Int)
    (hr : r ∈ fkRectFaithfulShearDartRoute ((x, y), (3 : Fin 4)))
    (he : r ∈ fkRectFaithfulShearDartRoute e) :
    FKRectIntegralSquareDartsIncident ((x, y), 3) e := by
  rcases e with ⟨⟨a, b⟩, nu⟩
  rcases r with ⟨s, t⟩
  fin_cases nu <;>
    simp [fkRectFaithfulShearDartRoute, fkRectFaithfulShearPair,
      FKRectIntegralSquareDartsIncident,
      fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY, Prod.ext_iff] at hr he ⊢ <;>
    omega



theorem fkRectIntegralSquareDartsIncident_of_mem_faithfulRoutes
    (d e : FKRectIntegralSquareDart) (r : Int × Int)
    (hr : r ∈ fkRectFaithfulShearDartRoute d)
    (he : r ∈ fkRectFaithfulShearDartRoute e) :
    FKRectIntegralSquareDartsIncident d e := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  · exact fkRectFaithfulRoutes_incident_from_0 x y e r hr he
  · exact fkRectFaithfulRoutes_incident_from_1 x y e r hr he
  · exact fkRectFaithfulRoutes_incident_from_2 x y e r hr he
  · exact fkRectFaithfulRoutes_incident_from_3 x y e r hr he


theorem fkRectIntegralSquareDartsIncident_of_faithfulRouteSite
    (d e : FKRectIntegralSquareDart) (r s : Int × Int)
    (hr : r ∈ fkRectFaithfulShearDartRoute d)
    (hs : s ∈ fkRectFaithfulShearDartRoute e)
    (hsite : fkRectPairSite r = fkRectPairSite s) :
    FKRectIntegralSquareDartsIncident d e := by
  have hrs : r = s := fkRectPairSite_injective hsite
  subst s
  exact fkRectIntegralSquareDartsIncident_of_mem_faithfulRoutes d e r hr hs

private theorem fkRectPairSite_adj_of_unit
    (p q : Int × Int)
    (h : (p.1 - q.1).natAbs + (p.2 - q.2).natAbs = 1) :
    (hypercubicLattice 2).Adj (fkRectPairSite p) (fkRectPairSite q) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simpa [fkRectPairSite] using h



theorem exists_fkRectFaithfulShearDartWalk
    (d : FKRectIntegralSquareDart) :
    ∃ W : (hypercubicLattice 2).Walk
        (fkRectFaithfulShearPoint d.1)
        (fkRectFaithfulShearPoint (fkRectIntegralSquareDartEnd d)),
      ∀ z ∈ W.support,
        ∃ r ∈ fkRectFaithfulShearDartRoute d, z = fkRectPairSite r := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu
  all_goals
    simp only [fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY]
  all_goals
    let a := fkRectFaithfulShearPair (x, y)
  · let b : Int × Int := (a.1 + 1, a.2)
    let c : Int × Int := (a.1 + 1, a.2 + 1)
    let e : Int × Int := (a.1 + 1, a.2 + 2)
    let f : Int × Int := (a.1 + 2, a.2 + 2)
    have hab := fkRectPairSite_adj_of_unit a b (by simp [b])
    have hbc := fkRectPairSite_adj_of_unit b c (by simp [b, c])
    have hce := fkRectPairSite_adj_of_unit c e (by simp [c, e])
    have hef := fkRectPairSite_adj_of_unit e f (by simp [e, f])
    let W : (hypercubicLattice 2).Walk (fkRectPairSite a)
        (fkRectPairSite f) := .cons hab (.cons hbc (.cons hce (.cons hef .nil)))
    have hstart : fkRectFaithfulShearPoint (x, y) = fkRectPairSite a := rfl
    have hend : fkRectFaithfulShearPoint (x + 1, y + 0) = fkRectPairSite f := by
      funext i
      fin_cases i <;> simp [fkRectFaithfulShearPoint,
        fkRectFaithfulShearPair, fkRectPairSite, a, f] <;> ring
    refine ⟨W.copy hstart.symm hend.symm, ?_⟩
    intro z hz
    simp only [W, Walk.support_copy, Walk.support_cons, Walk.support_nil,
      List.mem_cons, List.mem_singleton] at hz
    simpa [fkRectFaithfulShearDartRoute, a, b, c, e, f] using hz
  · let b : Int × Int := (a.1, a.2 - 1)
    let c : Int × Int := (a.1 + 1, a.2 - 1)
    let e : Int × Int := (a.1 + 2, a.2 - 1)
    let f : Int × Int := (a.1 + 2, a.2 - 2)
    have hab := fkRectPairSite_adj_of_unit a b (by simp [b])
    have hbc := fkRectPairSite_adj_of_unit b c (by simp [b, c])
    have hce := fkRectPairSite_adj_of_unit c e (by simp [c, e])
    have hef := fkRectPairSite_adj_of_unit e f (by simp [e, f])
    let W : (hypercubicLattice 2).Walk (fkRectPairSite a)
        (fkRectPairSite f) := .cons hab (.cons hbc (.cons hce (.cons hef .nil)))
    have hstart : fkRectFaithfulShearPoint (x, y) = fkRectPairSite a := rfl
    have hend : fkRectFaithfulShearPoint (x + 0, y + 1) = fkRectPairSite f := by
      funext i
      fin_cases i <;> simp [fkRectFaithfulShearPoint,
        fkRectFaithfulShearPair, fkRectPairSite, a, f] <;> ring
    refine ⟨W.copy hstart.symm hend.symm, ?_⟩
    intro z hz
    simp only [W, Walk.support_copy, Walk.support_cons, Walk.support_nil,
      List.mem_cons, List.mem_singleton] at hz
    simpa [fkRectFaithfulShearDartRoute, a, b, c, e, f] using hz
  · let b : Int × Int := (a.1 - 1, a.2)
    let c : Int × Int := (a.1 - 1, a.2 - 1)
    let e : Int × Int := (a.1 - 1, a.2 - 2)
    let f : Int × Int := (a.1 - 2, a.2 - 2)
    have hab := fkRectPairSite_adj_of_unit a b (by simp [b])
    have hbc := fkRectPairSite_adj_of_unit b c (by simp [b, c])
    have hce := fkRectPairSite_adj_of_unit c e (by simp [c, e])
    have hef := fkRectPairSite_adj_of_unit e f (by simp [e, f])
    let W : (hypercubicLattice 2).Walk (fkRectPairSite a)
        (fkRectPairSite f) := .cons hab (.cons hbc (.cons hce (.cons hef .nil)))
    have hstart : fkRectFaithfulShearPoint (x, y) = fkRectPairSite a := rfl
    have hend : fkRectFaithfulShearPoint (x + -1, y + 0) = fkRectPairSite f := by
      funext i
      fin_cases i <;> simp [fkRectFaithfulShearPoint,
        fkRectFaithfulShearPair, fkRectPairSite, a, f] <;> ring
    refine ⟨W.copy hstart.symm hend.symm, ?_⟩
    intro z hz
    simp only [W, Walk.support_copy, Walk.support_cons, Walk.support_nil,
      List.mem_cons, List.mem_singleton] at hz
    simpa [fkRectFaithfulShearDartRoute, a, b, c, e, f] using hz
  · let b : Int × Int := (a.1, a.2 + 1)
    let c : Int × Int := (a.1 - 1, a.2 + 1)
    let e : Int × Int := (a.1 - 2, a.2 + 1)
    let f : Int × Int := (a.1 - 2, a.2 + 2)
    have hab := fkRectPairSite_adj_of_unit a b (by simp [b])
    have hbc := fkRectPairSite_adj_of_unit b c (by simp [b, c])
    have hce := fkRectPairSite_adj_of_unit c e (by simp [c, e])
    have hef := fkRectPairSite_adj_of_unit e f (by simp [e, f])
    let W : (hypercubicLattice 2).Walk (fkRectPairSite a)
        (fkRectPairSite f) := .cons hab (.cons hbc (.cons hce (.cons hef .nil)))
    have hstart : fkRectFaithfulShearPoint (x, y) = fkRectPairSite a := rfl
    have hend : fkRectFaithfulShearPoint (x + 0, y + -1) = fkRectPairSite f := by
      funext i
      fin_cases i <;> simp [fkRectFaithfulShearPoint,
        fkRectFaithfulShearPair, fkRectPairSite, a, f] <;> ring
    refine ⟨W.copy hstart.symm hend.symm, ?_⟩
    intro z hz
    simp only [W, Walk.support_copy, Walk.support_cons, Walk.support_nil,
      List.mem_cons, List.mem_singleton] at hz
    simpa [fkRectFaithfulShearDartRoute, a, b, c, e, f] using hz




theorem FKRectIntegralSquareDartPath.exists_faithfulShearWalk
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) :
    ∃ V : (hypercubicLattice 2).Walk
        (fkRectFaithfulShearPoint p) (fkRectFaithfulShearPoint q),
      ∀ z ∈ V.support,
        z = fkRectFaithfulShearPoint p ∨
          ∃ d ∈ l, ∃ r ∈ fkRectFaithfulShearDartRoute d,
            z = fkRectPairSite r := by
  induction h with
  | nil p =>
      refine ⟨.nil, ?_⟩
      intro z hz
      simp only [Walk.support_nil, List.mem_singleton] at hz
      exact Or.inl hz
  | @cons d q r l hend tail ih =>
      obtain ⟨W, hW⟩ := exists_fkRectFaithfulShearDartWalk d
      obtain ⟨V, hV⟩ := ih
      let W' : (hypercubicLattice 2).Walk
          (fkRectFaithfulShearPoint d.1) (fkRectFaithfulShearPoint q) :=
        W.copy rfl (congrArg fkRectFaithfulShearPoint hend)
      refine ⟨W'.append V, ?_⟩
      intro z hz
      rw [Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · have hzW : z ∈ W.support := by simpa [W'] using hz
        obtain ⟨a, ha, rfl⟩ := hW z hzW
        exact Or.inr ⟨d, by simp, a, ha, rfl⟩
      · rcases hV z hz with hz | ⟨e, he, a, ha, rfl⟩
        · obtain ⟨a, ha, haeq⟩ := hW _ W.end_mem_support
          exact Or.inr ⟨d, by simp, a, ha, by simpa [hend, hz] using haeq⟩
        · exact Or.inr ⟨e, by simp [he], a, ha, rfl⟩

end

end StatMech.FrontierD
