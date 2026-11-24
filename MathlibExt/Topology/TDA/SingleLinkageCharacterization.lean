/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.TDA.SingleLinkage
public import Mathlib.Data.Fintype.EquivFin

/-!
# The Carlsson–Mémoli characterization of single linkage

G. Carlsson and F. Mémoli, *Characterization, stability and convergence of hierarchical
clustering methods*, JMLR 11 (2010) 1425–1470, Theorem 18: single linkage is the only
hierarchical clustering method, i.e. the only assignment of an ultrametric to every finite metric
space, satisfying

* (I) the two-point space at distance `δ > 0` is sent to itself;
* (II) functoriality: if `φ : X → Y` does not increase distances, then
  `u_Y (φ x) (φ x') ≤ u_X x x'`;
* (III) `u x x' ≥ sep(X, d)` for `x ≠ x'`, where `sep` is the smallest nonzero distance.

Both halves are proved: single linkage satisfies (I)–(III) (`slDist_axioms`), and any method
satisfying them is single linkage (`eq_slDist_of_axioms`). Finite metric spaces are encoded as a
finite type `X : Type` with a function `d : X → X → ℝ` satisfying `IsMetricFn`. The proof of
uniqueness follows the source's two steps; in step (B) we collapse the `r`-equivalence classes to
a space with a constant metric instead of the source's quotient path metric, which suffices.
-/

@[expose] public section

open Relation

namespace MathlibExt.Topology.TDA

/-- **Metric on a set, as a function.** `d` is symmetric, zero exactly on the diagonal and
satisfies the triangle inequality, so `(X, d)` is a metric space in the sense of Carlsson and
Mémoli, JMLR 11 (2010), §2 (their finite metric spaces). It overlaps `CSLibExt`'s
`MetricTSP.IsMetricCost`; `MathlibExt` cannot import `CSLibExt`, and Mathlib's metric classes are
instance-based (one metric per type), which does not fit comparing several dissimilarities on one
set. -/
structure IsMetricFn {X : Type*} (d : X → X → ℝ) : Prop where
  /-- Symmetry. -/
  symm : ∀ x y, d x y = d y x
  /-- Zero on the diagonal. -/
  self : ∀ x, d x x = 0
  /-- Positive off the diagonal. -/
  pos : ∀ x y, x ≠ y → 0 < d x y
  /-- The triangle inequality. -/
  triangle : ∀ x y z, d x z ≤ d x y + d y z

/-- **Ultrametric on a set, as a function.** A metric satisfying the strong triangle inequality
`u x z ≤ max (u x y) (u y z)` (Carlsson and Mémoli, JMLR 11 (2010), §2). It duplicates
`CSLibExt`'s `Bioinformatics.Phylogenetics.Splits.IsUltrametric` (same fields, the triangle
inequality there following from the three-point condition), which `MathlibExt` cannot import;
Mathlib's `IsUltrametricDist` is instance-based. -/
structure IsUltrametricFn {X : Type*} (u : X → X → ℝ) : Prop extends IsMetricFn u where
  /-- The strong triangle inequality. -/
  ultra : ∀ x y z, u x z ≤ max (u x y) (u y z)

/-- **The two-point metric space.** The space `{p, q}` with `d(p, q) = δ`, here on `Bool`; the
space `({p, q}, (0 δ; δ 0))` of Carlsson and Mémoli, JMLR 11 (2010), Thm. 18 (I). -/
def twoPointDist (δ : ℝ) : Bool → Bool → ℝ := fun a b => if a = b then 0 else δ

theorem isMetricFn_twoPointDist {δ : ℝ} (hδ : 0 < δ) : IsMetricFn (twoPointDist δ) where
  symm a b := by unfold twoPointDist; by_cases h : a = b <;> simp [h, eq_comm]
  self a := by simp [twoPointDist]
  pos a b h := by simp [twoPointDist, h, hδ]
  triangle a b c := by
    unfold twoPointDist
    by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hac : a = c <;>
      simp_all <;> linarith

/-- **Candidate hierarchical clustering methods.** An assignment of a function `X → X → ℝ` to
every dissimilarity on every finite type; `IsHCMethod` asks that metrics be sent to ultrametrics
(Carlsson and Mémoli, JMLR 11 (2010), Def. 11). -/
abbrev HCMethod : Type 1 := ∀ (X : Type) [Finite X], (X → X → ℝ) → X → X → ℝ

/-- **Hierarchical clustering method.** `T` sends every finite metric space to an ultrametric on
the same set (Carlsson and Mémoli, JMLR 11 (2010), Def. 11, with dendrograms identified with
ultrametrics by their Thm. 9). -/
def IsHCMethod (T : HCMethod) : Prop :=
  ∀ (X : Type) [Finite X] (d : X → X → ℝ), IsMetricFn d → IsUltrametricFn (T X d)

/-- **Condition (I).** The two-point metric space at distance `δ > 0` is sent to itself
(Carlsson and Mémoli, JMLR 11 (2010), Thm. 18 (I)). -/
def CMConditionI (T : HCMethod) : Prop :=
  ∀ δ : ℝ, 0 < δ → T Bool (twoPointDist δ) = twoPointDist δ

/-- **Condition (II), functoriality.** If `φ : X → Y` between finite metric spaces satisfies
`d_X x x' ≥ d_Y (φ x) (φ x')`, then `u_X x x' ≥ u_Y (φ x) (φ x')` (Carlsson and Mémoli, JMLR 11
(2010), Thm. 18 (II)). -/
def CMConditionII (T : HCMethod) : Prop :=
  ∀ (X Y : Type) [Finite X] [Finite Y] (dX : X → X → ℝ) (dY : Y → Y → ℝ),
    IsMetricFn dX → IsMetricFn dY → ∀ φ : X → Y, (∀ x x', dY (φ x) (φ x') ≤ dX x x') →
      ∀ x x', T Y dY (φ x) (φ x') ≤ T X dX x x'

/-- **Condition (III).** Points are never merged below the separation of the space: if every
nonzero distance is at least `s`, then `u x x' ≥ s` for `x ≠ x'` (Carlsson and Mémoli, JMLR 11
(2010), Thm. 18 (III), `u(x, x') ≥ sep(X, d)`). -/
def CMConditionIII (T : HCMethod) : Prop :=
  ∀ (X : Type) [Finite X] (d : X → X → ℝ), IsMetricFn d → ∀ x x', x ≠ x' →
    ∀ s : ℝ, (∀ a b, a ≠ b → s ≤ d a b) → s ≤ T X d x x'

section Lemmas

variable {X : Type*}

/-- **Below the separation, clusters are singletons.** If every distance between distinct points
is at least `s` and `r < s`, then `r`-equivalent points are equal (Carlsson and Mémoli, JMLR 11
(2010), Remark 19 on condition (III): the dendrogram is the partition into singletons for
`t < sep(X, d)`). -/
theorem eq_of_slEquiv_of_lt {d : X → X → ℝ} {r s : ℝ} (hs : ∀ a b, a ≠ b → s ≤ d a b)
    (hrs : r < s) {x y : X} (h : SLEquiv d r x y) : x = y := by
  induction h with
  | rel a b hab =>
    by_contra hne
    linarith [hs a b hne]
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **Single linkage never merges below the separation.** If every distance between distinct
points is at least `s`, then `u*(x, y) ≥ s` for `x ≠ y` (the fact that `T*` satisfies condition
(III) of Carlsson and Mémoli, JMLR 11 (2010), Thm. 18). -/
theorem le_slDist_of_sep {d : X → X → ℝ} {s : ℝ} (hs : ∀ a b, a ≠ b → s ≤ d a b) {x y : X}
    (hxy : x ≠ y) : s ≤ slDist d x y := by
  refine le_csInf (slDist_set_nonempty d x y) fun r ⟨_, h⟩ => ?_
  by_contra hlt
  exact hxy (eq_of_slEquiv_of_lt hs (not_le.1 hlt) h)

/-- **Single linkage outputs an ultrametric.** On a finite metric space, `u*` is an ultrametric:
symmetric, zero exactly on the diagonal and satisfying the strong triangle inequality (Carlsson
and Mémoli, JMLR 11 (2010), Example 7: `T*` is a hierarchical clustering method). -/
theorem isUltrametricFn_slDist [Finite X] {d : X → X → ℝ} (hd : IsMetricFn d) :
    IsUltrametricFn (slDist d) where
  symm := slDist_comm d
  self := slDist_self d
  pos x y hxy := by
    by_contra h
    have h0 : SLEquiv d 0 x y := (slEquiv_iff_slDist_le le_rfl).2 (not_lt.1 h)
    have hsep : ∀ a b, a ≠ b → (0 : ℝ) < d a b := hd.pos
    induction h0 with
    | rel a b hab =>
      by_cases hab' : a = b
      · exact hxy hab'
      · linarith [hsep a b hab']
    | refl a => exact hxy rfl
    | symm a b _ ih => exact ih (fun h => hxy h.symm) (by rwa [slDist_comm])
    | trans a b c h₁ h₂ ih₁ ih₂ =>
      by_cases hab : a = b
      · subst hab
        exact ih₂ hxy h
      · exact ih₁ hab (by
          have := slDist_nonneg d a b
          have := (slEquiv_iff_slDist_le le_rfl).1 h₁
          linarith)
  triangle x y z := (slDist_le_max d x y z).trans
    (max_le (le_add_of_nonneg_right (slDist_nonneg d y z))
      (le_add_of_nonneg_left (slDist_nonneg d x y)))
  ultra := slDist_le_max d

end Lemmas

/-- **Single linkage satisfies the Carlsson–Mémoli axioms.** `T*` is a hierarchical clustering
method satisfying conditions (I), (II) and (III), so the hypotheses of Carlsson and Mémoli,
JMLR 11 (2010), Thm. 18 are consistent and single linkage is the method that theorem
characterizes. -/
theorem slDist_axioms :
    IsHCMethod (fun _ _ d => slDist d) ∧ CMConditionI (fun _ _ d => slDist d) ∧
      CMConditionII (fun _ _ d => slDist d) ∧ CMConditionIII (fun _ _ d => slDist d) := by
  refine ⟨fun X _ d hd => isUltrametricFn_slDist hd, fun δ hδ => ?_, ?_, ?_⟩
  · funext a b
    by_cases hab : a = b
    · subst hab
      simp [slDist_self, twoPointDist]
    · refine le_antisymm ?_ ?_
      · calc slDist (twoPointDist δ) a b ≤ twoPointDist δ a b :=
              slDist_le (by simp [twoPointDist, hab, hδ.le])
          _ = twoPointDist δ a b := rfl
      · have : twoPointDist δ a b = δ := by simp [twoPointDist, hab]
        rw [this]
        exact le_slDist_of_sep (fun c e hce => by simp [twoPointDist, hce]) hab
  · intro X Y _ _ dX dY _ _ φ hφ x x'
    refine le_csInf (slDist_set_nonempty dX x x') fun r ⟨hr, h⟩ => ?_
    exact slDist_le_of_slEquiv hr (h.map φ hφ)
  · intro X _ d _ x x' hxx' s hs
    exact le_slDist_of_sep hs hxx'

/-- **Characterization of single linkage (Carlsson–Mémoli).** A hierarchical clustering method
satisfying conditions (I), (II) and (III) is single linkage: `T X d = u*` for every finite metric
space `(X, d)` (Carlsson and Mémoli, JMLR 11 (2010), Thm. 18). -/
theorem eq_slDist_of_axioms {T : HCMethod} (hT : IsHCMethod T) (h1 : CMConditionI T)
    (h2 : CMConditionII T) (h3 : CMConditionIII T) {X : Type} [Finite X] {d : X → X → ℝ}
    (hd : IsMetricFn d) : T X d = slDist d := by
  classical
  have hu := hT X d hd
  -- Step (A): `T X d ≤ d` pointwise, by mapping two-point spaces into `X`.
  have hud : ∀ x y, T X d x y ≤ d x y := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      rw [hu.self, hd.self]
    · have hδ : 0 < d x y := hd.pos x y hxy
      let φ : Bool → X := fun b => if b then x else y
      have hφ : ∀ a b, d (φ a) (φ b) ≤ twoPointDist (d x y) a b := by
        intro a b
        cases a <;> cases b <;> simp [φ, twoPointDist, hd.self, hd.symm y x]
      have := h2 Bool X (twoPointDist (d x y)) d (isMetricFn_twoPointDist hδ) hd φ hφ true false
      rw [h1 _ hδ] at this
      simpa [φ, twoPointDist] using this
  have hA : ∀ x y, T X d x y ≤ slDist d x y :=
    le_slDist hud hu.self hu.symm hu.ultra
  -- Step (B): `u* ≤ T X d`, by collapsing the `r`-equivalence classes for `r = T X d x x'`.
  funext x x'
  refine le_antisymm (hA x x') (not_lt.1 fun hlt => ?_)
  set r := T X d x x' with hr_def
  have hr0 : 0 ≤ r := by
    by_cases hxx : x = x'
    · subst hxx
      rw [hr_def, hu.self]
    · exact (hu.pos x x' hxx).le
  have hnot : ¬ SLEquiv d r x x' := fun h =>
    absurd (slDist_le_of_slEquiv hr0 h) (not_le.2 hlt)
  have e := SLEquiv.equivalence d r
  have : Fintype X := Fintype.ofFinite X
  -- A scale `c > r` below every distance between `r`-inequivalent points.
  obtain ⟨c, hrc, hc⟩ : ∃ c, r < c ∧ ∀ a b, ¬ SLEquiv d r a b → c ≤ d a b := by
    let F := (Finset.univ : Finset (X × X)).filter fun p => ¬ SLEquiv d r p.1 p.2
    have hF : F.Nonempty := ⟨(x, x'), Finset.mem_filter.2 ⟨Finset.mem_univ _, hnot⟩⟩
    obtain ⟨p, hpF, hpmin⟩ := F.exists_min_image (fun p => d p.1 p.2) hF
    refine ⟨d p.1 p.2, ?_, fun a b hab =>
      hpmin (a, b) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hab⟩)⟩
    by_contra hle
    exact (Finset.mem_filter.1 hpF).2 (EqvGen.rel _ _ (not_lt.1 hle))
  let Q := Quot (SLEquiv d r)
  let dQ : Q → Q → ℝ := fun z z' => if z = z' then 0 else c
  have hc0 : 0 < c := hr0.trans_lt hrc
  have hdQ : IsMetricFn dQ :=
    { symm := fun z z' => by
        simp only [dQ]
        by_cases h : z = z' <;> simp [h, eq_comm]
      self := fun z => by simp [dQ]
      pos := fun z z' h => by simp [dQ, h, hc0]
      triangle := fun z z' z'' => by
        simp only [dQ]
        by_cases h₁ : z = z' <;> by_cases h₂ : z' = z'' <;> by_cases h₃ : z = z'' <;>
          simp_all <;> linarith }
  have hmk : ∀ a b, Quot.mk (SLEquiv d r) a = Quot.mk _ b ↔ SLEquiv d r a b := fun a b =>
    ⟨fun h => e.eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩
  have hφ : ∀ a b, dQ (Quot.mk _ a) (Quot.mk _ b) ≤ d a b := by
    intro a b
    by_cases hab : SLEquiv d r a b
    · have : dQ (Quot.mk _ a) (Quot.mk _ b) = 0 := by simp [dQ, (hmk a b).2 hab]
      rw [this]
      by_cases h : a = b
      · rw [h, hd.self]
      · exact (hd.pos a b h).le
    · have : dQ (Quot.mk _ a) (Quot.mk _ b) = c := by simp [dQ, mt (hmk a b).1 hab]
      rw [this]
      exact hc a b hab
  have hII := h2 X Q d dQ hd hdQ (Quot.mk _) hφ x x'
  have hne : Quot.mk (SLEquiv d r) x ≠ Quot.mk _ x' := mt (hmk x x').1 hnot
  have hIII := h3 Q dQ hdQ _ _ hne c fun z z' h => by simp [dQ, h]
  linarith

end MathlibExt.Topology.TDA
