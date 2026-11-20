/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectFaithfulPrimalConfinement



open SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section



theorem fkRectFaithfulShearDartRoute_translate_fst
    (t : Int × Int) (d : FKRectIntegralSquareDart) (r : Int × Int)
    (hr : r ∈ fkRectFaithfulShearDartRoute
      (fkRectIntegralSquareDartTranslate t d)) :
    ∃ s ∈ fkRectFaithfulShearDartRoute d,
      r.1 = s.1 + 2 * (t.1 + t.2) := by
  have hroute : fkRectFaithfulShearDartRoute
      (fkRectIntegralSquareDartTranslate t d) =
      (fkRectFaithfulShearDartRoute d).map
        (fun s =>
          (s.1 + 2 * (t.1 + t.2), s.2 + 2 * (t.1 - t.2))) := by
    rcases d with ⟨⟨x, y⟩, mu⟩
    fin_cases mu <;>
      simp [fkRectIntegralSquareDartTranslate,
        fkRectFaithfulShearDartRoute, fkRectFaithfulShearPair,
        Prod.ext_iff] <;> ring <;> simp
  rw [hroute] at hr
  obtain ⟨s, hs, hrs⟩ := List.mem_map.mp hr
  refine ⟨s, hs, ?_⟩
  rw [← hrs]



theorem fkRectRepeatTranslatedDartPath_mem
    (l : List FKRectIntegralSquareDart) (u : Int × Int) (n : Nat)
    {d : FKRectIntegralSquareDart}
    (hd : d ∈ fkRectRepeatTranslatedDartPath l u n) :
    ∃ i : Nat, ∃ a ∈ l,
      d = fkRectIntegralSquareDartTranslate (fkRectNatScale i u) a := by
  induction n with
  | zero => simp [fkRectRepeatTranslatedDartPath] at hd
  | succ n ih =>
      rw [fkRectRepeatTranslatedDartPath, List.mem_append] at hd
      rcases hd with hd | hd
      · exact ih hd
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
        exact ⟨n, a, ha, rfl⟩



theorem fkRectRepeatTranslatedDartPath_faithfulRoute_fst_bounds
    (l : List FKRectIntegralSquareDart) (u : Int × Int) (n : Nat)
    (hu : u.1 + u.2 = 0) (left right : Int)
    (hbase : ∀ d ∈ l, ∀ r ∈ fkRectFaithfulShearDartRoute d,
      left ≤ r.1 ∧ r.1 ≤ right)
    {d : FKRectIntegralSquareDart} {r : Int × Int}
    (hd : d ∈ fkRectRepeatTranslatedDartPath l u n)
    (hr : r ∈ fkRectFaithfulShearDartRoute d) :
    left ≤ r.1 ∧ r.1 ≤ right := by
  obtain ⟨i, a, ha, rfl⟩ :=
    fkRectRepeatTranslatedDartPath_mem l u n hd
  obtain ⟨s, hs, hrs⟩ :=
    fkRectFaithfulShearDartRoute_translate_fst
      (fkRectNatScale i u) a r hr
  have hi : (fkRectNatScale i u).1 + (fkRectNatScale i u).2 = 0 := by
    simp [fkRectNatScale]
    linear_combination (i : Int) * hu
  have hb := hbase a ha s hs
  rw [hi] at hrs
  simp only [mul_zero, add_zero] at hrs
  omega

theorem fkRectRepeatTranslatedDartPath_ne_nil
    (l : List FKRectIntegralSquareDart) (u : Int × Int) (n : Nat)
    (hl : l ≠ []) (hn : 0 < n) :
    fkRectRepeatTranslatedDartPath l u n ≠ [] := by
  cases n with
  | zero => omega
  | succ n =>
      simp [fkRectRepeatTranslatedDartPath, hl]




theorem exists_fkRectFaithfulRepeatedVerticalWalk_fst_bounds
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    {x : R.Vertex}
    {w : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk x x}
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (halong : FKRectRefinedOpenWalkBlocksAlong R F w p q l)
    (hpath : FKRectIntegralSquareDartPath
      (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))
      (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q)) l)
    (hl : l ≠ []) (right : Nat)
    (hsupport : ∀ v ∈ w.support,
      1 ≤ v.1.val ∧ v.1.val ≤ right)
    (hpcol : p.1 = (x.1.val : Int))
    (hw : fkRectWalkWinding R w = (0, 1))
    (n : Nat) (hn : 0 < n) :
    let P := fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)
    ∃ V : (hypercubicLattice 2).Walk
        (fkRectFaithfulShearPoint P)
        ![(fkRectFaithfulShearPoint P) 0,
          (fkRectFaithfulShearPoint P) 1 +
            (n : Int) * (8 * (R.height : Int))],
      ∀ z ∈ V.support,
        16 ≤ z 0 ∧ z 0 ≤ 16 * (right : Int) + 8 := by
  dsimp only
  let P := fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)
  let Q := fkRectRefinedScalePoint (fkRectSquareDevelopPoint q)
  let u : Int × Int := (Q.1 - P.1, Q.2 - P.2)
  have hpath' : FKRectIntegralSquareDartPath P
      (P.1 + u.1, P.2 + u.2) l := by
    convert hpath using 1 <;> simp [P, Q, u] <;> ring
  have hrep := hpath'.repeatTranslated n
  have hfaithfulEnd :=
    halong.toSquareWalkLift R F |>.closed_faithfulRefined_end_of_verticalOne
      R hw
  have huHorizontal : u.1 + u.2 = 0 := by
    have hx := congrFun hfaithfulEnd 0
    simp only [Matrix.cons_val_zero] at hx
    change 2 * (Q.1 + Q.2) = 2 * (P.1 + P.2) at hx
    dsimp [u]
    omega
  have huVertical : 2 * (u.1 - u.2) = 8 * (R.height : Int) := by
    have hy := congrFun hfaithfulEnd 1
    simp only [Matrix.cons_val_one] at hy
    change 2 * (Q.1 - Q.2) =
      2 * (P.1 - P.2) + 8 * (R.height : Int) at hy
    dsimp [u]
    omega
  have hne := fkRectRepeatTranslatedDartPath_ne_nil l u n hl hn
  obtain ⟨V, hV⟩ := hrep.exists_faithfulShearWalk_of_ne_nil hne
  have hend : fkRectFaithfulShearPoint
      (P.1 + (n : Int) * u.1, P.2 + (n : Int) * u.2) =
      ![(fkRectFaithfulShearPoint P) 0,
        (fkRectFaithfulShearPoint P) 1 +
          (n : Int) * (8 * (R.height : Int))] := by
    rw [fkRectFaithfulShearPoint_add P
      ((n : Int) * u.1, (n : Int) * u.2)]
    funext i
    fin_cases i
    · change (fkRectFaithfulShearPoint P) 0 +
          2 * ((n : Int) * u.1 + (n : Int) * u.2) =
        (fkRectFaithfulShearPoint P) 0
      linear_combination (2 * (n : Int)) * huHorizontal
    · change (fkRectFaithfulShearPoint P) 1 +
          2 * ((n : Int) * u.1 - (n : Int) * u.2) =
        (fkRectFaithfulShearPoint P) 1 +
          (n : Int) * (8 * (R.height : Int))
      linear_combination (n : Int) * huVertical
  let V' := V.copy rfl hend
  refine ⟨V', ?_⟩
  intro z hz
  have hzV : z ∈ V.support := by simpa [V'] using hz
  obtain ⟨d, hd, r, hr, rfl⟩ := hV z hzV
  have hbase : ∀ d ∈ l, ∀ r ∈ fkRectFaithfulShearDartRoute d,
      16 ≤ r.1 ∧ r.1 ≤ 16 * (right : Int) + 8 := by
    intro d hd r hr
    exact halong.faithfulRoute_fst_bounds R F right
      hsupport hpcol hd hr
  have hrBounds :=
    fkRectRepeatTranslatedDartPath_faithfulRoute_fst_bounds
      l u n huHorizontal 16 (16 * (right : Int) + 8)
      hbase hd hr
  simpa [fkRectPairSite] using hrBounds

end

end StatMech.FrontierD
