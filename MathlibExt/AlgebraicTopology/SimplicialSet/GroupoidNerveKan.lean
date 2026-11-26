/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.AlgebraicTopology.Quasicategory.StrictSegal
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Groupoid

/-!
# Nerves of groupoids are Kan complexes

The nerve of an arbitrary small groupoid is a Kan complex. Inner horns are
filled by the strict Segal structure of a categorical nerve. The two outer
two-horns recover their missing arrow with `Groupoid.inv`; the only exceptional
three-dimensional outer equations are the corresponding cancellation laws.
From dimension four onward every vertex, edge, and triangle belongs to the
horn, so strict Segal reconstruction from the spine supplies the filler.
-/

@[expose] public section

open CategoryTheory Opposite SimplexCategory SimplicialObject

open scoped Simplicial

namespace SSet

universe u v

private def nerveChain {G : Type u} [Category.{v} G] {n : ℕ}
    (phi : Δ[n] ⟶ CategoryTheory.nerve G) : ComposableArrows G n :=
  SSet.yonedaEquiv phi

private def chainYoneda {G : Type u} [Category.{v} G] {n : ℕ}
    (s : ComposableArrows G n) : Δ[n] ⟶ CategoryTheory.nerve G :=
  (SSet.yonedaEquiv (X := CategoryTheory.nerve G) (n := ⦋n⦌)).symm s

private def deltaChain {G : Type u} [Category.{v} G] {n : ℕ}
    (i : Fin (n + 2)) (s : ComposableArrows G (n + 1)) : ComposableArrows G n :=
  (CategoryTheory.nerve G).δ i s

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
private lemma nerveChain_chainYoneda {G : Type u} [Category.{v} G]
    {n : ℕ} (s : ComposableArrows G n) : nerveChain (chainYoneda s) = s := by
  exact Equiv.apply_symm_apply
    (SSet.yonedaEquiv (X := CategoryTheory.nerve G) (n := ⦋n⦌)) s

@[simp]
private lemma nerveChain_delta_comp {G : Type u} [Category.{v} G]
    {n : ℕ} (i : Fin (n + 2)) (phi : Δ[n + 1] ⟶ CategoryTheory.nerve G) :
    nerveChain (SSet.stdSimplex.δ i ≫ phi) =
      (CategoryTheory.nerve G).δ i (nerveChain phi) :=
  SSet.stdSimplex.yonedaEquiv_δ_comp phi i

private lemma eq_of_nerveChain_eq {G : Type u} [Category.{v} G] {n : ℕ}
    {phi psi : Δ[n] ⟶ CategoryTheory.nerve G}
    (h : nerveChain phi = nerveChain psi) : phi = psi :=
  SSet.yonedaEquiv.injective h

private lemma delta_chainYoneda {G : Type u} [Category.{v} G] {n : ℕ}
    (i : Fin (n + 2)) (s : ComposableArrows G (n + 1)) :
    SSet.stdSimplex.δ i ≫ chainYoneda s =
      chainYoneda ((CategoryTheory.nerve G).δ i s) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
  exact nerveChain_chainYoneda (G := G) ((CategoryTheory.nerve G).δ i s)

private theorem innerHornFiller (G : Type u) [Groupoid.{v} G]
    {n : ℕ} {i : Fin (n + 2)} (h0 : 0 < i)
    (hn : i < Fin.last (n + 1))
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ CategoryTheory.nerve G)
    (hf : horn.IsCompatible f) :
    ∃ phi : Δ[n + 1] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ phi = f j hj := by
  let _ : Quasicategory (CategoryTheory.nerve G) :=
    StrictSegal.quasicategory (CategoryTheory.Nerve.strictSegal G)
  obtain ⟨phi, hphi⟩ := Quasicategory.hornFilling h0 hn hf.desc
  refine ⟨phi, fun j hj => ?_⟩
  rw [← hf.ι_desc j hj, hphi, ← Category.assoc, horn.ι_ι]

private theorem oneHornFiller (G : Type u) [Groupoid.{v} G]
    (i : Fin 2) (f : ∀ (j : Fin 2) (_ : j ≠ i), Δ[0] ⟶ CategoryTheory.nerve G) :
    ∃ phi : Δ[1] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin 2) (hj : j ≠ i), stdSimplex.δ j ≫ phi = f j hj := by
  fin_cases i
  · let h10 : (1 : Fin 2) ≠ 0 := by decide
    let x := SSet.yonedaEquiv (f 1 h10)
    let sigma : ComposableArrows G 1 := ComposableArrows.mk₁ (𝟙 x.left)
    refine ⟨SSet.yonedaEquiv.symm sigma, ?_⟩
    intro j hj
    fin_cases j
    · contradiction
    · have hp : hj = h10 := Subsingleton.elim _ _
      subst hp
      apply SSet.yonedaEquiv.injective
      rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
      change (CategoryTheory.nerve G).δ 1 sigma = x
      exact ComposableArrows.ext₀ rfl
  · let h01 : (0 : Fin 2) ≠ 1 := by decide
    let x := SSet.yonedaEquiv (f 0 h01)
    let sigma : ComposableArrows G 1 := ComposableArrows.mk₁ (𝟙 x.left)
    refine ⟨SSet.yonedaEquiv.symm sigma, ?_⟩
    intro j hj
    fin_cases j
    · have hp : hj = h01 := Subsingleton.elim _ _
      subst hp
      apply SSet.yonedaEquiv.injective
      rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
      change (CategoryTheory.nerve G).δ 0 sigma = x
      exact ComposableArrows.ext₀ rfl
    · contradiction

private theorem twoHornZeroFiller (G : Type u) [Groupoid.{v} G]
    (f : ∀ (j : Fin 3) (_ : j ≠ (0 : Fin 3)), Δ[1] ⟶ CategoryTheory.nerve G)
    (hf : horn.IsCompatible f) :
    ∃ phi : Δ[2] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin 3) (hj : j ≠ (0 : Fin 3)), stdSimplex.δ j ≫ phi = f j hj := by
  let h10 : (1 : Fin 3) ≠ 0 := by decide
  let h20 : (2 : Fin 3) ≠ 0 := by decide
  let s1 : ComposableArrows G 1 := SSet.yonedaEquiv (f 1 h10)
  let s2 : ComposableArrows G 1 := SSet.yonedaEquiv (f 2 h20)
  obtain ⟨A1, C, d, hd⟩ := ComposableArrows.mk₁_surjective s1
  obtain ⟨A2, B, a, ha⟩ := ComposableArrows.mk₁_surjective s2
  have hc := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (1 : Fin 3) (2 : Fin 3) h10 h20 (by decide))
  simp only [SSet.stdSimplex.yonedaEquiv_δ_comp] at hc
  change (CategoryTheory.nerve G).δ 1 s1 = (CategoryTheory.nerve G).δ 1 s2 at hc
  rw [hd, ha] at hc
  have hA := congrArg (fun q : ComposableArrows G 0 => q.obj 0) hc
  change A1 = A2 at hA
  subst A2
  let sigma : ComposableArrows G 2 :=
    ComposableArrows.mk₂ a (Groupoid.inv a ≫ d)
  refine ⟨SSet.yonedaEquiv.symm sigma, ?_⟩
  intro j hj
  fin_cases j
  · contradiction
  · have hp : hj = h10 := Subsingleton.elim _ _
    subst hp
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
    change (CategoryTheory.nerve G).δ 1 sigma = s1
    rw [hd]
    unfold sigma
    rw [CategoryTheory.nerve.δ₁_mk₂_eq]
    simp
    rfl
  · have hp : hj = h20 := Subsingleton.elim _ _
    subst hp
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
    change (CategoryTheory.nerve G).δ 2 sigma = s2
    rw [ha]
    unfold sigma
    rw [CategoryTheory.nerve.δ₂_mk₂_eq]

private theorem twoHornInnerFiller (G : Type u) [Groupoid.{v} G]
    (f : ∀ (j : Fin 3) (_ : j ≠ (1 : Fin 3)), Δ[1] ⟶ CategoryTheory.nerve G)
    (hf : horn.IsCompatible f) :
    ∃ phi : Δ[2] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin 3) (hj : j ≠ (1 : Fin 3)), stdSimplex.δ j ≫ phi = f j hj := by
  let h01 : (0 : Fin 3) ≠ 1 := by decide
  let h21 : (2 : Fin 3) ≠ 1 := by decide
  let s0 : ComposableArrows G 1 := SSet.yonedaEquiv (f 0 h01)
  let s2 : ComposableArrows G 1 := SSet.yonedaEquiv (f 2 h21)
  obtain ⟨B0, C, b, hb⟩ := ComposableArrows.mk₁_surjective s0
  obtain ⟨A, B2, a, ha⟩ := ComposableArrows.mk₁_surjective s2
  have hc := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (0 : Fin 3) (2 : Fin 3) h01 h21 (by decide))
  simp only [SSet.stdSimplex.yonedaEquiv_δ_comp] at hc
  change (CategoryTheory.nerve G).δ 1 s0 = (CategoryTheory.nerve G).δ 0 s2 at hc
  rw [hb, ha] at hc
  have hB := congrArg (fun q : ComposableArrows G 0 => q.obj 0) hc
  change B0 = B2 at hB
  subst B2
  let sigma : ComposableArrows G 2 := ComposableArrows.mk₂ a b
  refine ⟨SSet.yonedaEquiv.symm sigma, ?_⟩
  intro j hj
  fin_cases j
  · have hp : hj = h01 := Subsingleton.elim _ _
    subst hp
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
    change (CategoryTheory.nerve G).δ 0 sigma = s0
    rw [hb]
    unfold sigma
    rw [CategoryTheory.nerve.δ₀_mk₂_eq]
  · contradiction
  · have hp : hj = h21 := Subsingleton.elim _ _
    subst hp
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
    change (CategoryTheory.nerve G).δ 2 sigma = s2
    rw [ha]
    unfold sigma
    rw [CategoryTheory.nerve.δ₂_mk₂_eq]

private theorem twoHornLastFiller (G : Type u) [Groupoid.{v} G]
    (f : ∀ (j : Fin 3) (_ : j ≠ (2 : Fin 3)), Δ[1] ⟶ CategoryTheory.nerve G)
    (hf : horn.IsCompatible f) :
    ∃ phi : Δ[2] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin 3) (hj : j ≠ (2 : Fin 3)), stdSimplex.δ j ≫ phi = f j hj := by
  let h02 : (0 : Fin 3) ≠ 2 := by decide
  let h12 : (1 : Fin 3) ≠ 2 := by decide
  let s0 : ComposableArrows G 1 := SSet.yonedaEquiv (f 0 h02)
  let s1 : ComposableArrows G 1 := SSet.yonedaEquiv (f 1 h12)
  obtain ⟨B, C0, b, hb⟩ := ComposableArrows.mk₁_surjective s0
  obtain ⟨A, C1, d, hd⟩ := ComposableArrows.mk₁_surjective s1
  have hc := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (0 : Fin 3) (1 : Fin 3) h02 h12 (by decide))
  simp only [SSet.stdSimplex.yonedaEquiv_δ_comp] at hc
  change (CategoryTheory.nerve G).δ 0 s0 = (CategoryTheory.nerve G).δ 0 s1 at hc
  rw [hb, hd] at hc
  have hC := congrArg (fun q : ComposableArrows G 0 => q.obj 0) hc
  change C0 = C1 at hC
  subst C1
  let sigma : ComposableArrows G 2 :=
    ComposableArrows.mk₂ (d ≫ Groupoid.inv b) b
  refine ⟨SSet.yonedaEquiv.symm sigma, ?_⟩
  intro j hj
  fin_cases j
  · have hp : hj = h02 := Subsingleton.elim _ _
    subst hp
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
    change (CategoryTheory.nerve G).δ 0 sigma = s0
    rw [hb]
    unfold sigma
    rw [CategoryTheory.nerve.δ₀_mk₂_eq]
  · have hp : hj = h12 := Subsingleton.elim _ _
    subst hp
    apply SSet.yonedaEquiv.injective
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
    change (CategoryTheory.nerve G).δ 1 sigma = s1
    rw [hd]
    unfold sigma
    rw [CategoryTheory.nerve.δ₁_mk₂_eq]
    simp
    rfl
  · contradiction

private lemma outerZeroThreeCancellation {G : Type u} [Groupoid.{v} G]
    {A B C D : G} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (d : A ⟶ C) (e : B ⟶ D)
    (h13 : d = a ≫ b) (h12 : d ≫ c = a ≫ e) : e = b ≫ c := by
  have hh : Groupoid.inv a ≫ (d ≫ c) = Groupoid.inv a ≫ (a ≫ e) :=
    congrArg (fun q : A ⟶ D => Groupoid.inv a ≫ q) h12
  rw [h13] at hh
  simpa [Category.assoc] using hh.symm

private lemma outerLastThreeCancellation {G : Type u} [Groupoid.{v} G]
    {A B C D : G} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (d : A ⟶ C) (e : B ⟶ D)
    (h02 : e = b ≫ c) (h12 : d ≫ c = a ≫ e) : d = a ≫ b := by
  have hh : (d ≫ c) ≫ Groupoid.inv c = (a ≫ e) ≫ Groupoid.inv c :=
    congrArg (fun q : A ⟶ D => q ≫ Groupoid.inv c) h12
  rw [h02] at hh
  simpa [Category.assoc] using hh

private theorem normalizeOuterZero {G : Type u} [Groupoid.{v} G]
    (f : ∀ (j : Fin 4) (_ : j ≠ (0 : Fin 4)), Δ[2] ⟶ CategoryTheory.nerve G)
    (hf : horn.IsCompatible f) :
    ∃ (A B C D : G) (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D),
      nerveChain (f 1 (by decide)) = ComposableArrows.mk₂ (a ≫ b) c ∧
      nerveChain (f 2 (by decide)) = ComposableArrows.mk₂ a (b ≫ c) ∧
      nerveChain (f 3 (by decide)) = ComposableArrows.mk₂ a b := by
  let h10 : (1 : Fin 4) ≠ 0 := by decide
  let h20 : (2 : Fin 4) ≠ 0 := by decide
  let h30 : (3 : Fin 4) ≠ 0 := by decide
  let s1 : ComposableArrows G 2 := nerveChain (f 1 h10)
  let s2 : ComposableArrows G 2 := nerveChain (f 2 h20)
  let s3 : ComposableArrows G 2 := nerveChain (f 3 h30)
  obtain ⟨A1, C1, D1, d, c, hs1⟩ := ComposableArrows.mk₂_surjective s1
  obtain ⟨A2, B2, D2, a2, e, hs2⟩ := ComposableArrows.mk₂_surjective s2
  obtain ⟨A3, B3, C3, a3, b, hs3⟩ := ComposableArrows.mk₂_surjective s3
  have h12 := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (1 : Fin 4) (2 : Fin 4) h10 h20 (by decide))
  have h13 := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (1 : Fin 4) (3 : Fin 4) h10 h30 (by decide))
  have h23 := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (2 : Fin 4) (3 : Fin 4) h20 h30 (by decide))
  simp only [SSet.stdSimplex.yonedaEquiv_δ_comp] at h12 h13 h23
  change (CategoryTheory.nerve G).δ 1 s1 = (CategoryTheory.nerve G).δ 1 s2 at h12
  change (CategoryTheory.nerve G).δ 2 s1 = (CategoryTheory.nerve G).δ 1 s3 at h13
  change (CategoryTheory.nerve G).δ 2 s2 = (CategoryTheory.nerve G).δ 2 s3 at h23
  rw [hs1, hs2, CategoryTheory.nerve.δ₁_mk₂_eq,
    CategoryTheory.nerve.δ₁_mk₂_eq] at h12
  rw [hs1, hs3, CategoryTheory.nerve.δ₂_mk₂_eq,
    CategoryTheory.nerve.δ₁_mk₂_eq] at h13
  rw [hs2, hs3, CategoryTheory.nerve.δ₂_mk₂_eq,
    CategoryTheory.nerve.δ₂_mk₂_eq] at h23
  have hA23 := congrArg (fun q : ComposableArrows G 1 => q.obj 0) h23
  change A2 = A3 at hA23
  subst A3
  have hB23 := congrArg (fun q : ComposableArrows G 1 => q.obj 1) h23
  change B2 = B3 at hB23
  subst B3
  have ha23 : Arrow.mk a2 = Arrow.mk a3 :=
    congrArg ComposableArrows.arrowEquiv h23
  have ha23' : a2 = a3 := (Arrow.mk_inj A2 B2).mp ha23
  subst a3
  have hA13 := congrArg (fun q : ComposableArrows G 1 => q.obj 0) h13
  change A1 = A2 at hA13
  subst A1
  have hC13 := congrArg (fun q : ComposableArrows G 1 => q.obj 1) h13
  change C1 = C3 at hC13
  subst C1
  have hd13 : Arrow.mk d = Arrow.mk (a2 ≫ b) :=
    congrArg ComposableArrows.arrowEquiv h13
  have hd13' : d = a2 ≫ b := (Arrow.mk_inj A2 C3).mp hd13
  subst d
  have hD12 := congrArg (fun q : ComposableArrows G 1 => q.obj 1) h12
  change D1 = D2 at hD12
  subst D2
  have htotal : Arrow.mk ((a2 ≫ b) ≫ c) = Arrow.mk (a2 ≫ e) :=
    congrArg ComposableArrows.arrowEquiv h12
  have htotal' : (a2 ≫ b) ≫ c = a2 ≫ e :=
    (Arrow.mk_inj A2 D1).mp htotal
  have he : e = b ≫ c :=
    outerZeroThreeCancellation a2 b c (a2 ≫ b) e rfl htotal'
  subst e
  refine ⟨A2, B2, C3, D1, a2, b, c, ?_, ?_, ?_⟩
  · simpa [s1] using hs1
  · simpa [s2] using hs2
  · simpa [s3] using hs3

private theorem normalizeOuterLast {G : Type u} [Groupoid.{v} G]
    (f : ∀ (j : Fin 4) (_ : j ≠ (3 : Fin 4)), Δ[2] ⟶ CategoryTheory.nerve G)
    (hf : horn.IsCompatible f) :
    ∃ (A B C D : G) (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D),
      nerveChain (f 0 (by decide)) = ComposableArrows.mk₂ b c ∧
      nerveChain (f 1 (by decide)) = ComposableArrows.mk₂ (a ≫ b) c ∧
      nerveChain (f 2 (by decide)) = ComposableArrows.mk₂ a (b ≫ c) := by
  let h03 : (0 : Fin 4) ≠ 3 := by decide
  let h13 : (1 : Fin 4) ≠ 3 := by decide
  let h23 : (2 : Fin 4) ≠ 3 := by decide
  let s0 : ComposableArrows G 2 := nerveChain (f 0 h03)
  let s1 : ComposableArrows G 2 := nerveChain (f 1 h13)
  let s2 : ComposableArrows G 2 := nerveChain (f 2 h23)
  obtain ⟨B0, C0, D0, b0, c0, hs0⟩ := ComposableArrows.mk₂_surjective s0
  obtain ⟨A1, C1, D1, d, c1, hs1⟩ := ComposableArrows.mk₂_surjective s1
  obtain ⟨A2, B2, D2, a2, e, hs2⟩ := ComposableArrows.mk₂_surjective s2
  have h01 := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (0 : Fin 4) (1 : Fin 4) h03 h13 (by decide))
  have h02 := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (0 : Fin 4) (2 : Fin 4) h03 h23 (by decide))
  have h12 := congrArg SSet.yonedaEquiv
    (hf.δ_pred_comp (1 : Fin 4) (2 : Fin 4) h13 h23 (by decide))
  simp only [SSet.stdSimplex.yonedaEquiv_δ_comp] at h01 h02 h12
  change (CategoryTheory.nerve G).δ 0 s0 = (CategoryTheory.nerve G).δ 0 s1 at h01
  change (CategoryTheory.nerve G).δ 1 s0 = (CategoryTheory.nerve G).δ 0 s2 at h02
  change (CategoryTheory.nerve G).δ 1 s1 = (CategoryTheory.nerve G).δ 1 s2 at h12
  rw [hs0, hs1, CategoryTheory.nerve.δ₀_mk₂_eq,
    CategoryTheory.nerve.δ₀_mk₂_eq] at h01
  rw [hs0, hs2, CategoryTheory.nerve.δ₁_mk₂_eq,
    CategoryTheory.nerve.δ₀_mk₂_eq] at h02
  rw [hs1, hs2, CategoryTheory.nerve.δ₁_mk₂_eq,
    CategoryTheory.nerve.δ₁_mk₂_eq] at h12
  have hC01 := congrArg (fun q : ComposableArrows G 1 => q.obj 0) h01
  change C0 = C1 at hC01
  subst C1
  have hD01 := congrArg (fun q : ComposableArrows G 1 => q.obj 1) h01
  change D0 = D1 at hD01
  subst D1
  have hc01 : Arrow.mk c0 = Arrow.mk c1 :=
    congrArg ComposableArrows.arrowEquiv h01
  have hc01' : c0 = c1 := (Arrow.mk_inj C0 D0).mp hc01
  subst c1
  have hB02 := congrArg (fun q : ComposableArrows G 1 => q.obj 0) h02
  change B0 = B2 at hB02
  subst B2
  have hD02 := congrArg (fun q : ComposableArrows G 1 => q.obj 1) h02
  change D0 = D2 at hD02
  subst D2
  have he02 : Arrow.mk (b0 ≫ c0) = Arrow.mk e :=
    congrArg ComposableArrows.arrowEquiv h02
  have he02' : b0 ≫ c0 = e := (Arrow.mk_inj B0 D0).mp he02
  subst e
  have hA12 := congrArg (fun q : ComposableArrows G 1 => q.obj 0) h12
  change A1 = A2 at hA12
  subst A1
  have htotal : Arrow.mk (d ≫ c0) = Arrow.mk (a2 ≫ (b0 ≫ c0)) :=
    congrArg ComposableArrows.arrowEquiv h12
  have htotal' : d ≫ c0 = a2 ≫ (b0 ≫ c0) :=
    (Arrow.mk_inj A2 D0).mp htotal
  have hd : d = a2 ≫ b0 :=
    outerLastThreeCancellation a2 b0 c0 d (b0 ≫ c0) rfl htotal'
  subst d
  refine ⟨A2, B0, C0, D0, a2, b0, c0, ?_, ?_, ?_⟩
  · simpa [s0] using hs0
  · simpa [s1] using hs1
  · simpa [s2] using hs2

private lemma castPred_two (h : (2 : Fin 4) ≠ Fin.last 3) :
    (2 : Fin 4).castPred h = (2 : Fin 3) := by
  apply Fin.ext
  rfl

private theorem innerThreeFamilyCompatible {G : Type u} [Category.{v} G]
    {A B C D : G} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) :
    let g : ∀ (j : Fin 4) (_ : j ≠ (1 : Fin 4)),
        Δ[2] ⟶ CategoryTheory.nerve G := fun j _ =>
      if j = 0 then chainYoneda (ComposableArrows.mk₂ b c)
      else if j = 2 then chainYoneda (ComposableArrows.mk₂ a (b ≫ c))
      else chainYoneda (ComposableArrows.mk₂ a b)
    horn.IsCompatible g := by
  dsimp only
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  fin_cases j <;> fin_cases k <;> simp_all
  all_goals simp only [Fin.lt_def] at hjk
  all_goals try omega
  all_goals
    rw [delta_chainYoneda, delta_chainYoneda]
    simp only [CategoryTheory.nerve.δ₀_mk₂_eq,
      CategoryTheory.nerve.δ₁_mk₂_eq, CategoryTheory.nerve.δ₂_mk₂_eq]
  rw [castPred_two, CategoryTheory.nerve.δ₂_mk₂_eq]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem faceOneOfCanonicalThree {G : Type u} [Category.{v} G]
    {A B C D : G} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (sigma : ComposableArrows G 3)
    (h0 : deltaChain 0 sigma = ComposableArrows.mk₂ b c)
    (h3 : deltaChain 3 sigma = ComposableArrows.mk₂ a b) :
    deltaChain 1 sigma = ComposableArrows.mk₂ (a ≫ b) c := by
  unfold deltaChain at h0 h3 ⊢
  let target : (CategoryTheory.nerve G) _⦋2⦌ := ComposableArrows.mk₂ (a ≫ b) c
  change (CategoryTheory.nerve G).δ 1 sigma = target
  apply (CategoryTheory.Nerve.strictSegal G).spineInjective
  apply Path.ext'
  intro k
  by_cases hk : k = 0
  · subst k
    dsimp only [StrictSegal.spineEquiv, spine_arrow, Function.comp_apply, Equiv.coe_fn_mk]
    rw [SimplexCategory.mkOfSucc_zero_eq_δ]
    change (CategoryTheory.nerve G).δ 2 ((CategoryTheory.nerve G).δ 1 sigma) =
      (CategoryTheory.nerve G).δ 2 target
    have hh := ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_δ'' (X := CategoryTheory.nerve G)
        (i := (1 : Fin 4)) (j := (2 : Fin 3)) (by decide)).symm sigma
    simp only [types_comp_apply] at hh
    have hi : (1 : Fin 4).castLT (by decide) = (1 : Fin 3) := by decide
    have hj : (2 : Fin 3).succ = (3 : Fin 4) := by decide
    rw [hi, hj] at hh
    rw [hh, h3, CategoryTheory.nerve.δ₁_mk₂_eq]
    unfold target
    rw [CategoryTheory.nerve.δ₂_mk₂_eq]
  · have hk1 : k = 1 := Fin.eq_one_of_ne_zero k hk
    subst k
    dsimp only [StrictSegal.spineEquiv, spine_arrow, Function.comp_apply, Equiv.coe_fn_mk]
    rw [SimplexCategory.mkOfSucc_one_eq_δ]
    change (CategoryTheory.nerve G).δ 0 ((CategoryTheory.nerve G).δ 1 sigma) =
      (CategoryTheory.nerve G).δ 0 target
    have hh := ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_δ (X := CategoryTheory.nerve G)
        (i := (0 : Fin 3)) (j := (0 : Fin 3)) (by decide)).symm sigma
    simp only [types_comp_apply] at hh
    have hi : (0 : Fin 3).castSucc = (0 : Fin 4) := by decide
    have hj : (0 : Fin 3).succ = (1 : Fin 4) := by decide
    rw [hi, hj] at hh
    rw [← hh, h0, CategoryTheory.nerve.δ₀_mk₂_eq]
    unfold target
    rw [CategoryTheory.nerve.δ₀_mk₂_eq]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem faceTwoOfCanonicalThree {G : Type u} [Category.{v} G]
    {A B C D : G} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (sigma : ComposableArrows G 3)
    (h0 : deltaChain 0 sigma = ComposableArrows.mk₂ b c)
    (h3 : deltaChain 3 sigma = ComposableArrows.mk₂ a b) :
    deltaChain 2 sigma = ComposableArrows.mk₂ a (b ≫ c) := by
  unfold deltaChain at h0 h3 ⊢
  let target : (CategoryTheory.nerve G) _⦋2⦌ := ComposableArrows.mk₂ a (b ≫ c)
  change (CategoryTheory.nerve G).δ 2 sigma = target
  apply (CategoryTheory.Nerve.strictSegal G).spineInjective
  apply Path.ext'
  intro k
  by_cases hk : k = 0
  · subst k
    dsimp only [StrictSegal.spineEquiv, spine_arrow, Function.comp_apply, Equiv.coe_fn_mk]
    rw [SimplexCategory.mkOfSucc_zero_eq_δ]
    change (CategoryTheory.nerve G).δ 2 ((CategoryTheory.nerve G).δ 2 sigma) =
      (CategoryTheory.nerve G).δ 2 target
    have hh := ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_δ_self (X := CategoryTheory.nerve G)
        (i := (2 : Fin 3))).symm sigma
    simp only [types_comp_apply] at hh
    have hi : (2 : Fin 3).castSucc = (2 : Fin 4) := by decide
    have hj : (2 : Fin 3).succ = (3 : Fin 4) := by decide
    rw [hi, hj] at hh
    rw [← hh, h3, CategoryTheory.nerve.δ₂_mk₂_eq]
    unfold target
    rw [CategoryTheory.nerve.δ₂_mk₂_eq]
  · have hk1 : k = 1 := Fin.eq_one_of_ne_zero k hk
    subst k
    dsimp only [StrictSegal.spineEquiv, spine_arrow, Function.comp_apply, Equiv.coe_fn_mk]
    rw [SimplexCategory.mkOfSucc_one_eq_δ]
    change (CategoryTheory.nerve G).δ 0 ((CategoryTheory.nerve G).δ 2 sigma) =
      (CategoryTheory.nerve G).δ 0 target
    have hh := ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_δ (X := CategoryTheory.nerve G)
        (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)) sigma
    simp only [types_comp_apply] at hh
    have hi : (0 : Fin 3).castSucc = (0 : Fin 4) := by decide
    have hj : (1 : Fin 3).succ = (2 : Fin 4) := by decide
    rw [hi, hj] at hh
    rw [hh, h0, CategoryTheory.nerve.δ₁_mk₂_eq]
    unfold target
    rw [CategoryTheory.nerve.δ₀_mk₂_eq]

private theorem canonicalThreeSimplex {G : Type u} [Groupoid.{v} G]
    {A B C D : G} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) :
    ∃ phi : Δ[3] ⟶ CategoryTheory.nerve G,
      nerveChain (stdSimplex.δ 0 ≫ phi) = ComposableArrows.mk₂ b c ∧
      nerveChain (stdSimplex.δ 1 ≫ phi) = ComposableArrows.mk₂ (a ≫ b) c ∧
      nerveChain (stdSimplex.δ 2 ≫ phi) = ComposableArrows.mk₂ a (b ≫ c) ∧
      nerveChain (stdSimplex.δ 3 ≫ phi) = ComposableArrows.mk₂ a b := by
  let g : ∀ (j : Fin 4) (_ : j ≠ (1 : Fin 4)),
      Δ[2] ⟶ CategoryTheory.nerve G := fun j _ =>
    if j = 0 then chainYoneda (ComposableArrows.mk₂ b c)
    else if j = 2 then chainYoneda (ComposableArrows.mk₂ a (b ≫ c))
    else chainYoneda (ComposableArrows.mk₂ a b)
  have hg : horn.IsCompatible g := innerThreeFamilyCompatible a b c
  obtain ⟨phi, hphi⟩ :=
    innerHornFiller G (i := (1 : Fin 4)) (by decide) (by decide) g hg
  let sigma : ComposableArrows G 3 := nerveChain phi
  have h0 : deltaChain 0 sigma = ComposableArrows.mk₂ b c := by
    have hh := congrArg nerveChain (hphi (0 : Fin 4) (by decide))
    simpa [deltaChain, sigma, g] using hh
  have h3 : deltaChain 3 sigma = ComposableArrows.mk₂ a b := by
    have hh := congrArg nerveChain (hphi (3 : Fin 4) (by decide))
    simpa [deltaChain, sigma, g] using hh
  have h1 := faceOneOfCanonicalThree a b c sigma h0 h3
  have h2 := faceTwoOfCanonicalThree a b c sigma h0 h3
  refine ⟨phi, ?_, ?_, ?_, ?_⟩
  · simpa [deltaChain, sigma] using h0
  · simpa [deltaChain, sigma] using h1
  · simpa [deltaChain, sigma] using h2
  · simpa [deltaChain, sigma] using h3

private theorem threeHornZeroFiller (G : Type u) [Groupoid.{v} G]
    (f : ∀ (j : Fin 4) (_ : j ≠ (0 : Fin 4)), Δ[2] ⟶ CategoryTheory.nerve G)
    (hf : horn.IsCompatible f) :
    ∃ phi : Δ[3] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin 4) (hj : j ≠ (0 : Fin 4)), stdSimplex.δ j ≫ phi = f j hj := by
  obtain ⟨A, B, C, D, a, b, c, h1, h2, h3⟩ := normalizeOuterZero f hf
  obtain ⟨phi, h0phi, h1phi, h2phi, h3phi⟩ := canonicalThreeSimplex a b c
  refine ⟨phi, fun j hj => ?_⟩
  fin_cases j
  · contradiction
  · apply eq_of_nerveChain_eq
    exact h1phi.trans h1.symm
  · apply eq_of_nerveChain_eq
    exact h2phi.trans h2.symm
  · apply eq_of_nerveChain_eq
    exact h3phi.trans h3.symm

private theorem threeHornLastFiller (G : Type u) [Groupoid.{v} G]
    (f : ∀ (j : Fin 4) (_ : j ≠ (3 : Fin 4)), Δ[2] ⟶ CategoryTheory.nerve G)
    (hf : horn.IsCompatible f) :
    ∃ phi : Δ[3] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin 4) (hj : j ≠ (3 : Fin 4)), stdSimplex.δ j ≫ phi = f j hj := by
  obtain ⟨A, B, C, D, a, b, c, h0, h1, h2⟩ := normalizeOuterLast f hf
  obtain ⟨phi, h0phi, h1phi, h2phi, h3phi⟩ := canonicalThreeSimplex a b c
  refine ⟨phi, fun j hj => ?_⟩
  fin_cases j
  · apply eq_of_nerveChain_eq
    exact h0phi.trans h0.symm
  · apply eq_of_nerveChain_eq
    exact h1phi.trans h1.symm
  · apply eq_of_nerveChain_eq
    exact h2phi.trans h2.symm
  · contradiction

namespace horn

@[simps! vertex_coe arrow_coe]
private def highSpine (N : ℕ) (i : Fin (N + 1)) (hN : 3 ≤ N) :
    Path (Λ[N, i] : SSet.{u}) N :=
  Λ[N, i].liftPath (stdSimplex.spineId N)
    (fun _ => by
      rw [horn_obj_eq_univ i 0 (by omega)]
      trivial)
    (fun _ => by
      rw [horn_obj_eq_univ i 1 (by omega)]
      trivial)

end horn

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem highHornFiller {X : SSet.{u}} (sx : StrictSegal X) (m : ℕ)
    (i : Fin (m + 5)) (sigma0 : (Λ[m + 4, i] : SSet.{u}) ⟶ X) :
    ∃ sigma : X _⦋m + 4⦌, ∀ (j : Fin (m + 5)) (hj : j ≠ i),
      X.δ j sigma = sigma0.app _ (horn.face i j hj) := by
  use sx.spineToSimplex <| Path.map (horn.highSpine (m + 4) i (by omega)) sigma0
  intro j hj
  apply sx.spineInjective
  ext k
  dsimp only [StrictSegal.spineEquiv, spine_arrow, Function.comp_apply, Equiv.coe_fn_mk]
  rw [← types_comp_apply (sigma0.app _) (X.map _), ← sigma0.naturality]
  let ksucc := k.succ.castSucc
  obtain hlt | hgt | heq : ksucc < j ∨ j < ksucc ∨ j = ksucc := by lia
  · rw [← spine_arrow, StrictSegal.spine_δ_arrow_lt sx _ hlt]
    dsimp only [Path.map_arrow, spine_arrow, Fin.coe_eq_castSucc]
    dsimp
    apply congr_arg
    apply Subtype.ext
    rw [horn.highSpine_arrow_coe]
    dsimp [horn.face, CosimplicialObject.δ]
    rw [dsimp% Subcomplex.yonedaEquiv_coe, Subfunctor.lift_ι, stdSimplex.map_apply,
      Quiver.Hom.unop_op, SSet.yonedaEquiv_map, Equiv.apply_symm_apply,
      mkOfSucc_δ_lt hlt]
    rfl
  · rw [← spine_arrow, StrictSegal.spine_δ_arrow_gt sx _ hgt]
    dsimp
    apply congr_arg
    apply Subtype.ext
    rw [horn.highSpine_arrow_coe]
    dsimp [horn.face, CosimplicialObject.δ]
    rw [dsimp% Subcomplex.yonedaEquiv_coe, Subfunctor.lift_ι, stdSimplex.map_apply,
      Quiver.Hom.unop_op, SSet.yonedaEquiv_map, Equiv.apply_symm_apply,
      mkOfSucc_δ_gt hgt]
    rfl
  · let triangle : (Λ[m + 4, i] : SSet.{u}) _⦋2⦌ :=
      ⟨stdSimplex.triangle
        (⟨k.val, by omega⟩ : Fin (m + 5))
        (⟨k.val + 1, by omega⟩ : Fin (m + 5))
        (⟨k.val + 2, by omega⟩ : Fin (m + 5)) (by simp) (by simp), by
          rw [horn_obj_eq_univ i 2 (by omega)]
          trivial⟩
    have hi : ((horn.highSpine (m + 4) i (by omega)).map sigma0).interval k 2
        (by omega) = X.spine 2 (sigma0.app _ triangle) := by
      ext q
      dsimp [spine_arrow, Path.map_interval, Path.map_arrow]
      rw [← dsimp% sigma0.naturality_apply]
      apply congr_arg
      apply Subtype.ext
      rw [Path.arrow_interval (horn.highSpine (m + 4) i (by omega)) k 2 q
        (⟨k.val + q.val, by omega⟩ : Fin (m + 4)) (by omega) (by simp)]
      rw [horn.highSpine_arrow_coe]
      ext a : 1
      fin_cases a <;> fin_cases q <;> rfl
    rw [← spine_arrow, StrictSegal.spine_δ_arrow_eq sx _ heq, hi]
    simp only [StrictSegal.spineToDiagonal, diagonal, StrictSegal.spineToSimplex_spine_apply]
    rw [← types_comp_apply (sigma0.app _) (X.map _), ← sigma0.naturality, types_comp_apply]
    dsimp
    apply congr_arg
    apply Subtype.ext
    ext z : 1
    dsimp [horn.face]
    rw [dsimp% Subcomplex.yonedaEquiv_coe, Subfunctor.lift_ι, stdSimplex.map_apply,
      Quiver.Hom.unop_op, stdSimplex.map_apply, Quiver.Hom.unop_op]
    dsimp [CosimplicialObject.δ]
    rw [SSet.yonedaEquiv_map]
    simp only [Equiv.apply_symm_apply, triangle]
    rw [mkOfSucc_δ_eq heq]
    fin_cases z <;> rfl

private theorem highFamilyFiller (G : Type u) [Groupoid.{v} G] (m : ℕ)
    (i : Fin (m + 5))
    (f : ∀ (j : Fin (m + 5)) (_ : j ≠ i), Δ[m + 3] ⟶ CategoryTheory.nerve G)
    (hf : horn.IsCompatible f) :
    ∃ phi : Δ[m + 4] ⟶ CategoryTheory.nerve G,
      ∀ (j : Fin (m + 5)) (hj : j ≠ i), stdSimplex.δ j ≫ phi = f j hj := by
  obtain ⟨sigma, hsigma⟩ :=
    highHornFiller (CategoryTheory.Nerve.strictSegal G) m i hf.desc
  refine ⟨SSet.yonedaEquiv.symm sigma, fun j hj => ?_⟩
  apply SSet.yonedaEquiv.injective
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
  simp only [Equiv.apply_symm_apply]
  rw [hsigma j hj]
  have hh := congrArg SSet.yonedaEquiv (hf.ι_desc j hj)
  calc
    hf.desc.app _ (horn.face i j hj) =
        SSet.yonedaEquiv (horn.ι i j hj ≫ hf.desc) := by
      symm
      rw [horn.ι, SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply]
    _ = SSet.yonedaEquiv (f j hj) := hh

/-- The nerve of an arbitrary small groupoid is a Kan complex. -/
theorem kanComplex_nerve_of_groupoid (G : Type u) [CategoryTheory.Groupoid.{v} G] :
    SSet.KanComplex (CategoryTheory.nerve G) := by
  rw [SSet.KanComplex.iff]
  intro n i f hf
  cases n with
  | zero => exact oneHornFiller G i f
  | succ n =>
      cases n with
      | zero =>
          fin_cases i
          · exact twoHornZeroFiller G f hf
          · exact twoHornInnerFiller G f hf
          · exact twoHornLastFiller G f hf
      | succ n =>
          cases n with
          | zero =>
              fin_cases i
              · exact threeHornZeroFiller G f hf
              · exact innerHornFiller G (by decide) (by decide) f hf
              · exact innerHornFiller G (by decide) (by decide) f hf
              · exact threeHornLastFiller G f hf
          | succ m => exact highFamilyFiller G m i f hf

end SSet


universe u' v'

namespace SSet.StrictSegal

set_option backward.isDefEq.respectTransparency false in
/-- In dimension at least three, the original horn restriction determines
a simplex of a strict Segal simplicial set. -/
theorem eq_of_highHornRestriction_eq {X : SSet.{u'}} (sx : StrictSegal X)
    {n : ℕ} (i : Fin (n + 1)) (hn : 3 ≤ n) {s t : X _⦋n⦌}
    (h : (horn n i).ι ≫ yonedaEquiv.symm s =
      (horn n i).ι ≫ yonedaEquiv.symm t) : s = t := by
  apply sx.spineInjective
  change X.spine n s = X.spine n t
  apply Path.ext
  · funext j
    let a : (Δ[n] : SSet.{u'}) _⦋0⦌ :=
      stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋n⦌ j)
    have ha : a ∈ (horn n i).obj (op ⦋0⦌) := by
      rw [horn_obj_eq_univ i 0 (by omega)]
      trivial
    have hh := congrArg (fun f : (horn n i : SSet.{u'}) ⟶ X =>
      f.app (op ⦋0⦌) ⟨a, ha⟩) h
    change (yonedaEquiv.symm s).app (op ⦋0⦌) a =
      (yonedaEquiv.symm t).app (op ⦋0⦌) a at hh
    dsimp only [a] at hh
    change X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j).op s =
      X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ j).op t at hh
    exact hh
  · funext j
    let a : (Δ[n] : SSet.{u'}) _⦋1⦌ := stdSimplex.objEquiv.symm (mkOfSucc j)
    have ha : a ∈ (horn n i).obj (op ⦋1⦌) := by
      rw [horn_obj_eq_univ i 1 (by omega)]
      trivial
    have hh := congrArg (fun f : (horn n i : SSet.{u'}) ⟶ X =>
      f.app (op ⦋1⦌) ⟨a, ha⟩) h
    change (yonedaEquiv.symm s).app (op ⦋1⦌) a =
      (yonedaEquiv.symm t).app (op ⦋1⦌) a at hh
    dsimp only [a] at hh
    change X.map (mkOfSucc j).op s = X.map (mkOfSucc j).op t at hh
    exact hh

end SSet.StrictSegal

namespace CategoryTheory.nerve

set_option backward.isDefEq.respectTransparency false in
/-- A two-dimensional horn restriction determines a simplex in the actual
nerve of a groupoid, using cancellation for its two outer horns. -/
theorem eq_of_twoHornRestriction_eq (G : Type u') [Groupoid.{v'} G]
    (i : Fin 3) {s t : (nerve G) _⦋2⦌}
    (h : (SSet.horn 2 i).ι ≫ SSet.yonedaEquiv.symm s =
      (SSet.horn 2 i).ι ≫ SSet.yonedaEquiv.symm t) : s = t := by
  have faces : ∀ j : Fin 3, j ≠ i → (nerve G).δ j s = (nerve G).δ j t := by
    intro j hj
    let a : (Δ[2] : SSet.{max u' v'}) _⦋1⦌ :=
      SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ j)
    have ha : a ∈ (SSet.horn 2 i).obj (op ⦋1⦌) := by
      dsimp only [a]
      exact (SSet.objEquiv_symm_δ_mem_horn_iff j i).2 hj
    have hh := congrArg
      (fun f : (SSet.horn 2 i : SSet.{max u' v'}) ⟶ nerve G =>
        f.app (op ⦋1⦌) ⟨a, ha⟩) h
    change (SSet.yonedaEquiv.symm s).app (op ⦋1⦌) a =
      (SSet.yonedaEquiv.symm t).app (op ⦋1⦌) a at hh
    dsimp only [a] at hh
    change (nerve G).δ j s = (nerve G).δ j t at hh
    exact hh
  obtain ⟨A, B, C, f, g, rfl⟩ := ComposableArrows.mk₂_surjective s
  obtain ⟨A', B', C', f', g', rfl⟩ := ComposableArrows.mk₂_surjective t
  fin_cases i
  · have hf := faces 2 (by decide)
    have hfg := faces 1 (by decide)
    simp only [δ₂_mk₂_eq] at hf
    simp only [δ₁_mk₂_eq] at hfg
    have hA := congrArg (fun q : ComposableArrows G 1 => q.obj 0) hf
    change A = A' at hA
    subst A'
    have hB := congrArg (fun q : ComposableArrows G 1 => q.obj 1) hf
    change B = B' at hB
    subst B'
    have hC := congrArg (fun q : ComposableArrows G 1 => q.obj 1) hfg
    change C = C' at hC
    subst C'
    have hf' : f = f' := (Arrow.mk_inj _ _).1
      (congrArg (fun q : ComposableArrows G 1 => ComposableArrows.arrowEquiv q) hf)
    subst f'
    have hfg' : f ≫ g = f ≫ g' := (Arrow.mk_inj _ _).1
      (congrArg (fun q : ComposableArrows G 1 => ComposableArrows.arrowEquiv q) hfg)
    have hg' : g = g' := (cancel_epi f).1 hfg'
    subst g'
    rfl
  · have hf := faces 2 (by decide)
    have hg := faces 0 (by decide)
    simp only [δ₂_mk₂_eq] at hf
    simp only [δ₀_mk₂_eq] at hg
    have hA := congrArg (fun q : ComposableArrows G 1 => q.obj 0) hf
    change A = A' at hA
    subst A'
    have hB := congrArg (fun q : ComposableArrows G 1 => q.obj 1) hf
    change B = B' at hB
    subst B'
    have hC := congrArg (fun q : ComposableArrows G 1 => q.obj 1) hg
    change C = C' at hC
    subst C'
    have hf' : f = f' := (Arrow.mk_inj _ _).1
      (congrArg (fun q : ComposableArrows G 1 => ComposableArrows.arrowEquiv q) hf)
    subst f'
    have hg' : g = g' := (Arrow.mk_inj _ _).1
      (congrArg (fun q : ComposableArrows G 1 => ComposableArrows.arrowEquiv q) hg)
    subst g'
    rfl
  · have hg := faces 0 (by decide)
    have hfg := faces 1 (by decide)
    simp only [δ₀_mk₂_eq] at hg
    simp only [δ₁_mk₂_eq] at hfg
    have hA := congrArg (fun q : ComposableArrows G 1 => q.obj 0) hfg
    change A = A' at hA
    subst A'
    have hB := congrArg (fun q : ComposableArrows G 1 => q.obj 0) hg
    change B = B' at hB
    subst B'
    have hC := congrArg (fun q : ComposableArrows G 1 => q.obj 1) hg
    change C = C' at hC
    subst C'
    have hg' : g = g' := (Arrow.mk_inj _ _).1
      (congrArg (fun q : ComposableArrows G 1 => ComposableArrows.arrowEquiv q) hg)
    subst g'
    have hfg' : f ≫ g = f' ≫ g := (Arrow.mk_inj _ _).1
      (congrArg (fun q : ComposableArrows G 1 => ComposableArrows.arrowEquiv q) hfg)
    have hf' : f = f' := (cancel_mono g).1 hfg'
    subst f'
    rfl


/-- In every dimension at least two, the actual horn restriction determines
its simplex in the nerve of a groupoid. -/
theorem eq_of_hornRestriction_eq (G : Type u') [Groupoid.{v'} G]
    {n : ℕ} (i : Fin (n + 1)) (hn : 2 ≤ n) {s t : (nerve G) _⦋n⦌}
    (h : (SSet.horn n i).ι ≫ SSet.yonedaEquiv.symm s =
      (SSet.horn n i).ι ≫ SSet.yonedaEquiv.symm t) : s = t := by
  by_cases hn2 : n = 2
  · subst n
    exact eq_of_twoHornRestriction_eq G i h
  · exact SSet.StrictSegal.eq_of_highHornRestriction_eq
      (CategoryTheory.Nerve.strictSegal G) i (by omega) h

end CategoryTheory.nerve
