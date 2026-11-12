/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.GrahamFourColorBalancedCore
import Code.FrontierA.GrahamLemmaOneFourColor

open Finset
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent
open StatMech.GrahamGHS.FourColor

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]



def grahamToBalancedColor (U : Finset ι) (q : GrahamFourColoring ι) :
    ↑U -> Fin 4 := fun x =>
  if (x : ι) ∈ q.color1 then 0
  else if (x : ι) ∈ q.color2 then 1
  else if (x : ι) ∈ q.color3 then 2
  else 3

theorem mem_balanced_colorClass_iff
    (U : Finset ι) (c : ↑U -> Fin 4) (a : Fin 4) (i : ι) :
    i ∈ colorClass U c a ↔ ∃ hi : i ∈ U, c ⟨i, hi⟩ = a := by
  simp [colorClass]

theorem colorClass_grahamToBalancedColor_zero
    (U : Finset ι) (q : GrahamFourColoring ι)
    (hq : q.IsPartition U) :
    colorClass U (grahamToBalancedColor U q) 0 = q.color1 := by
  ext i
  rw [mem_balanced_colorClass_iff]
  constructor
  · rintro ⟨hi, hx⟩
    by_cases h1 : i ∈ q.color1 <;>
      by_cases h2 : i ∈ q.color2 <;>
      by_cases h3 : i ∈ q.color3 <;>
      simp [grahamToBalancedColor, h1, h2, h3] at hx ⊢
  · intro hi
    refine ⟨hq.1 hi, ?_⟩
    simp [grahamToBalancedColor, hi]

theorem colorClass_grahamToBalancedColor_one
    (U : Finset ι) (q : GrahamFourColoring ι)
    (hq : q.IsPartition U) :
    colorClass U (grahamToBalancedColor U q) 1 = q.color2 := by
  ext i
  rw [mem_balanced_colorClass_iff]
  constructor
  · rintro ⟨hiU, hx⟩
    by_cases h1 : i ∈ q.color1 <;>
      by_cases h2 : i ∈ q.color2 <;>
      by_cases h3 : i ∈ q.color3 <;>
      simp [grahamToBalancedColor, h1, h2, h3] at hx ⊢
  · intro hi
    have hiU := hq.2.1 hi
    have hi1 : i ∉ q.color1 := by
      intro hi1
      exact Finset.disjoint_left.mp hq.2.2.2.1 hi1 hi
    refine ⟨hiU, ?_⟩
    simp [grahamToBalancedColor, hi1, hi]

theorem colorClass_grahamToBalancedColor_two
    (U : Finset ι) (q : GrahamFourColoring ι)
    (hq : q.IsPartition U) :
    colorClass U (grahamToBalancedColor U q) 2 = q.color3 := by
  ext i
  rw [mem_balanced_colorClass_iff]
  constructor
  · rintro ⟨hiU, hx⟩
    by_cases h1 : i ∈ q.color1 <;>
      by_cases h2 : i ∈ q.color2 <;>
      by_cases h3 : i ∈ q.color3 <;>
      simp [grahamToBalancedColor, h1, h2, h3] at hx ⊢
  · intro hi
    have hiU := hq.2.2.1 hi
    have hi1 : i ∉ q.color1 := by
      intro hi1
      exact Finset.disjoint_left.mp hq.2.2.2.2.1 hi1 hi
    have hi2 : i ∉ q.color2 := by
      intro hi2
      exact Finset.disjoint_left.mp hq.2.2.2.2.2 hi2 hi
    refine ⟨hiU, ?_⟩
    simp [grahamToBalancedColor, hi1, hi2, hi]

theorem colorClass_grahamToBalancedColor_three
    (U : Finset ι) (q : GrahamFourColoring ι)
    (hq : q.IsPartition U) :
    colorClass U (grahamToBalancedColor U q) 3 = q.color4 U := by
  ext i
  rw [mem_balanced_colorClass_iff]
  simp only [GrahamFourColoring.color4, Finset.mem_sdiff,
    Finset.mem_union]
  constructor
  · rintro ⟨hiU, hx⟩
    by_cases h1 : i ∈ q.color1 <;>
      by_cases h2 : i ∈ q.color2 <;>
      by_cases h3 : i ∈ q.color3 <;>
      simp [grahamToBalancedColor, h1, h2, h3] at hx ⊢
    exact hiU
  · rintro ⟨hiU, hi⟩
    simp only [not_or] at hi
    refine ⟨hiU, ?_⟩
    simp [grahamToBalancedColor, hi.1.1, hi.1.2, hi.2]



theorem grahamToBalancedColor_leftPattern
    (ends : ι -> Sym2 W) (U : Finset ι) (j k l m : W)
    (q : GrahamFourColoring ι)
    (hq : q ∈ grahamLemmaOneSeparatedColorings ends U j k l m) :
    LeftPattern ends U {j, k} {k, l} k m
      (grahamToBalancedColor U q) := by
  rw [mem_grahamLemmaOneSeparatedColorings] at hq
  rcases hq with ⟨hpart, h1, h2, h3, h4, hd1, hd2⟩
  unfold LeftPattern RowsDisconnect
  rw [colorClass_grahamToBalancedColor_zero U q hpart,
    colorClass_grahamToBalancedColor_one U q hpart,
    colorClass_grahamToBalancedColor_two U q hpart,
    colorClass_grahamToBalancedColor_three U q hpart,
    rowClass_zero, rowClass_one,
    colorClass_grahamToBalancedColor_zero U q hpart,
    colorClass_grahamToBalancedColor_one U q hpart,
    colorClass_grahamToBalancedColor_two U q hpart,
    colorClass_grahamToBalancedColor_three U q hpart]
  exact ⟨h1, h2, h3, h4, hd1, hd2⟩




def balancedColorToGraham (U : Finset ι) (c : ↑U -> Fin 4) :
    GrahamFourColoring ι where
  color1 := colorClass U c 0
  color2 := colorClass U c 1
  color3 := colorClass U c 2

theorem balancedColorToGraham_color4
    (U : Finset ι) (c : ↑U -> Fin 4) :
    (balancedColorToGraham U c).color4 U = colorClass U c 3 := by
  ext i
  by_cases hi : i ∈ U
  · have hc : c ⟨i, hi⟩ = 0 ∨ c ⟨i, hi⟩ = 1 ∨
        c ⟨i, hi⟩ = 2 ∨ c ⟨i, hi⟩ = 3 := by omega
    rcases hc with hc | hc | hc | hc <;>
      simp [balancedColorToGraham, GrahamFourColoring.color4,
        mem_balanced_colorClass_iff, hi, hc]
  · simp only [balancedColorToGraham, GrahamFourColoring.color4,
      Finset.mem_sdiff, Finset.mem_union, mem_balanced_colorClass_iff]
    simp [hi]

theorem balancedColorToGraham_isPartition
    (U : Finset ι) (c : ↑U -> Fin 4) :
    (balancedColorToGraham U c).IsPartition U := by
  unfold GrahamFourColoring.IsPartition balancedColorToGraham
  exact ⟨colorClass_subset U c 0, colorClass_subset U c 1,
    colorClass_subset U c 2,
    colorClass_disjoint U c (by decide),
    colorClass_disjoint U c (by decide),
    colorClass_disjoint U c (by decide)⟩

theorem balancedColorToGraham_grahamToBalancedColor
    (U : Finset ι) (q : GrahamFourColoring ι)
    (hq : q.IsPartition U) :
    balancedColorToGraham U (grahamToBalancedColor U q) = q := by
  cases q
  rw [GrahamFourColoring.mk.injEq]
  exact ⟨colorClass_grahamToBalancedColor_zero U _ hq,
    colorClass_grahamToBalancedColor_one U _ hq,
    colorClass_grahamToBalancedColor_two U _ hq⟩

theorem grahamToBalancedColor_balancedColorToGraham
    (U : Finset ι) (c : ↑U -> Fin 4) :
    grahamToBalancedColor U (balancedColorToGraham U c) = c := by
  funext x
  have hc : c x = 0 ∨ c x = 1 ∨ c x = 2 ∨ c x = 3 := by omega
  rcases hc with hc | hc | hc | hc <;>
    simp [grahamToBalancedColor, balancedColorToGraham,
      mem_balanced_colorClass_iff, x.2, hc]

theorem balancedColorToGraham_mixed
    (ends : ι -> Sym2 W) (U : Finset ι) (j k l m : W)
    (c : ↑U -> Fin 4)
    (hc : RightPattern ends U {j, k} {k, l} k m c) :
    balancedColorToGraham U c ∈
      grahamLemmaOneMixedColorings ends U j k l m := by
  rw [mem_grahamLemmaOneMixedColorings]
  rcases hc with ⟨h1, h2, h3, h4, hd1, hd2⟩
  refine ⟨balancedColorToGraham_isPartition U c, h1, h2, h3, ?_, ?_⟩
  · simpa [balancedColorToGraham_color4 U c] using h4
  · simpa [balancedColorToGraham, rowClass_zero] using hd1




theorem grahamLemmaOne_card_le_of_balancedMinor
    (ends : ι -> Sym2 W) (U : Finset ι) (j k l m : W)
    (hminor : GrahamFiberMinor ends U j k l m) :
    #(grahamLemmaOneSeparatedColorings ends U j k l m) ≤
      #(grahamLemmaOneMixedColorings ends U j k l m) := by
  let sepToLeft :
      {q // q ∈ grahamLemmaOneSeparatedColorings ends U j k l m} ->
        leftFiber ends U {j, k} {k, l} k m := fun q =>
    ⟨grahamToBalancedColor U q.1,
      grahamToBalancedColor_leftPattern ends U j k l m q.1 q.2⟩
  have hsepInj : Function.Injective sepToLeft := by
    intro q r hqr
    apply Subtype.ext
    have hfun : grahamToBalancedColor U q.1 =
        grahamToBalancedColor U r.1 := congrArg Subtype.val hqr
    have hqpart :=
      (mem_grahamLemmaOneSeparatedColorings ends U j k l m q.1).mp q.2 |>.1
    have hrpart :=
      (mem_grahamLemmaOneSeparatedColorings ends U j k l m r.1).mp r.2 |>.1
    calc
      q.1 = balancedColorToGraham U (grahamToBalancedColor U q.1) :=
        (balancedColorToGraham_grahamToBalancedColor U q.1 hqpart).symm
      _ = balancedColorToGraham U (grahamToBalancedColor U r.1) :=
        congrArg (balancedColorToGraham U) hfun
      _ = r.1 := balancedColorToGraham_grahamToBalancedColor U r.1 hrpart
  let rightToMixed :
      rightFiber ends U {j, k} {k, l} k m ->
        {q // q ∈ grahamLemmaOneMixedColorings ends U j k l m} := fun c =>
    ⟨balancedColorToGraham U c.1,
      balancedColorToGraham_mixed ends U j k l m c.1 c.2⟩
  have hrightInj : Function.Injective rightToMixed := by
    intro c d hcd
    apply Subtype.ext
    have hgraham : balancedColorToGraham U c.1 =
        balancedColorToGraham U d.1 := congrArg Subtype.val hcd
    calc
      c.1 = grahamToBalancedColor U (balancedColorToGraham U c.1) :=
        (grahamToBalancedColor_balancedColorToGraham U c.1).symm
      _ = grahamToBalancedColor U (balancedColorToGraham U d.1) :=
        congrArg (grahamToBalancedColor U) hgraham
      _ = d.1 := grahamToBalancedColor_balancedColorToGraham U d.1
  calc
    #(grahamLemmaOneSeparatedColorings ends U j k l m) =
        Fintype.card
          ↥(grahamLemmaOneSeparatedColorings ends U j k l m) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card (leftFiber ends U {j, k} {k, l} k m) :=
      Fintype.card_le_of_injective sepToLeft hsepInj
    _ ≤ Fintype.card (rightFiber ends U {j, k} {k, l} k m) := hminor
    _ ≤ Fintype.card
          ↥(grahamLemmaOneMixedColorings ends U j k l m) :=
      Fintype.card_le_of_injective rightToMixed hrightInj
    _ = #(grahamLemmaOneMixedColorings ends U j k l m) := by
      exact Fintype.card_coe _




theorem grahamLemmaOne_card_le_of_total_disconnected
    (ends : ι -> Sym2 W) (U : Finset ι) (j k l m : W)
    (hdisc : ¬connK ends U k m) :
    #(grahamLemmaOneSeparatedColorings ends U j k l m) ≤
      #(grahamLemmaOneMixedColorings ends U j k l m) :=
  grahamLemmaOne_card_le_of_balancedMinor ends U j k l m
    (GrahamFiberMinor_of_total_disconnected ends U j k l m hdisc)

end StatMech.FrontierA
