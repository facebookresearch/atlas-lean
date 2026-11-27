/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Tactic.Ring

/-!
# OWR-1183-011: infinite transversals from points to spanned hyperplanes

`OWR1183Question_holds` matches every point of a spanning set to a distinct spanned hyperplane
containing it. For finite sets the proof establishes Hall’s condition by linear algebra.
For infinite sets it uses cardinal induction and separation by spanned hyperplanes.
-/

namespace MathlibExt.Geometry.InfiniteTransversalsSpannedHyperplanesWanted

@[expose] public section

/-! Source record `OWR-1183-011`. -/

namespace ITSP

/-!
# Clause inventory for [OWR-1183-011]

- Quantifier domain: dimension `d : ℕ` with `1 ≤ d`, ambient `Fin d → ℝ`.
- Quantifier domain: `P : Set (Fin d → ℝ)`.
- Hypothesis: `affineSpan ℝ P = ⊤` (spanning).
- Object: hyperplanes as level sets of nonzero linear functionals.
- Object: `H`, hyperplanes whose affine span is attained by some `Q ⊆ P`.
- Question: `∃ f : P → H` injective with `p ∈ f p` for all `p`.
-/

/-- **Affine hyperplanes in $\mathbb{R}^d$.** An affine subspace $A$ of $\mathbb{R}^d$ is an affine
hyperplane when there are a nonzero linear functional $\ell \colon \mathbb{R}^d \to \mathbb{R}$ and
a real number $c$ such that $A = \{x \in \mathbb{R}^d : \ell(x) = c\}$.

Source: `OWR-1183-011`. -/
def IsAffineHyperplane (d : ℕ) (Hp : AffineSubspace ℝ (Fin d → ℝ)) : Prop :=
  ∃ (l : (Fin d → ℝ) →ₗ[ℝ] ℝ) (c : ℝ), l ≠ 0 ∧ ∀ x, x ∈ Hp ↔ l x = c

/-- **Hyperplanes spanned by a point set.** For a set $P \subseteq \mathbb{R}^d$, the hyperplanes
spanned by $P$ are the affine hyperplanes of $\mathbb{R}^d$ that equal the affine span of some
subset of $P$.

Source: `OWR-1183-011`. -/
def SpannedHyperplaneSet (d : ℕ) (P : Set (Fin d → ℝ)) :
    Set (AffineSubspace ℝ (Fin d → ℝ)) :=
  {Hp | IsAffineHyperplane d Hp ∧ ∃ Q : Set (Fin d → ℝ), Q ⊆ P ∧ affineSpan ℝ Q = Hp}

/-- **Injective point-to-hyperplane matching question.** The statement that for every $d \ge 1$
and every set $P \subseteq \mathbb{R}^d$ whose affine span is all of $\mathbb{R}^d$, writing
$\mathcal{H}$ for the set of affine hyperplanes of $\mathbb{R}^d$ that equal the affine span of
some subset of $P$, there is an injective map $f \colon P \to \mathcal{H}$ with $p \in f(p)$ for
every $p \in P$.

Source: the question of `OWR-1183-011`. -/
def OWR1183Question : Prop :=
  ∀ (d : ℕ) (_hd : 1 ≤ d) (P : Set (Fin d → ℝ)), affineSpan ℝ P = ⊤ →
    ∃ f : P → ↥(SpannedHyperplaneSet d P),
      Function.Injective f ∧ ∀ p : P, p.val ∈ (f p).val

end ITSP

end

open AffineSubspace Module Set Cardinal
open scoped Cardinal

private abbrev Point (d : ℕ) := Fin d → ℝ
private abbrev Flat (d : ℕ) := AffineSubspace ℝ (Point d)
private noncomputable abbrev dim {d} (S : Flat d) := finrank ℝ S.direction
private abbrev extendFlat {d} (S : Flat d) (x : Point d) :=
  affineSpan ℝ (insert x (S : Set (Point d)))

variable {d : ℕ} {P : Set (Fin d → ℝ)}

private theorem dim_top : dim (⊤ : Flat d) = d := by
  rw [dim, AffineSubspace.direction_top ℝ (Point d) (Point d), finrank_top]
  simp

private theorem le_extend (S : Flat d) (x : Point d) : S ≤ extendFlat S x :=
  fun _ h ↦ mem_affineSpan ℝ (Set.mem_insert_of_mem x h)

private theorem mem_extend (S : Flat d) (x : Point d) : x ∈ extendFlat S x :=
  mem_affineSpan ℝ (Set.mem_insert x _)

private theorem dim_lt {S T : Flat d} (h : S < T) (hne : (S : Set (Point d)).Nonempty) :
    dim S < dim T := Submodule.finrank_lt_finrank_of_lt (direction_lt_of_nonempty h hne)

private theorem dim_extend {S : Flat d} (hne : (S : Set (Point d)).Nonempty)
    {x : Point d} (hx : x ∉ S) :
    dim (extendFlat S x) = dim S + 1 := by
  have hlt := dim_lt (lt_of_le_of_ne (le_extend S x) (fun he ↦ hx (he ▸ mem_extend S x))) hne
  have hle := finrank_vectorSpan_insert_le (k := ℝ) S x
  rw [← direction_affineSpan] at hle
  exact le_antisymm hle hlt

private theorem extend_le {S T : Flat d} {x : Point d} (hst : S ≤ T) (hx : x ∈ T) :
    extendFlat S x ≤ T := affineSpan_le.2 (Set.insert_subset hx hst)

private theorem extend_eq {S : Flat d} (hne : (S : Set (Point d)).Nonempty)
    {x y : Point d} (hx : x ∉ S) (hy : y ∉ S) (h : y ∈ extendFlat S x) :
    extendFlat S y = extendFlat S x := by
  refine (extend_le (le_extend S x) h).eq_of_not_lt fun hlt ↦ ?_
  have hdim := dim_lt hlt ⟨y, mem_extend S y⟩
  simp only [dim_extend hne hx, dim_extend hne hy, lt_self_iff_false] at hdim

private theorem isHyperplane_of_dim {S : Flat d} (hne : (S : Set (Point d)).Nonempty)
    (h : dim S + 1 = d) : ITSP.IsAffineHyperplane d S := by
  obtain ⟨o, ho⟩ := hne
  change finrank ℝ S.direction + 1 = d at h
  have hproper : S.direction < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro ht
    rw [ht, finrank_top, Module.finrank_pi, Fintype.card_fin] at h
    omega
  obtain ⟨l, hl, hker⟩ := S.direction.exists_le_ker_of_lt_top hproper
  have heq : S.direction = LinearMap.ker l := by
    apply hker.eq_of_not_lt
    intro hh
    have hlt := Submodule.finrank_lt_finrank_of_lt hh
    have hlt' := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr
      (mt LinearMap.ker_eq_top.mp hl) : LinearMap.ker l < ⊤)
    simp only [finrank_top, Module.finrank_pi, Fintype.card_fin] at hlt'
    omega
  refine ⟨l, l o, hl, fun x ↦ ?_⟩
  rw [← vsub_right_mem_direction_iff_mem ho, heq, LinearMap.mem_ker, vsub_eq_sub, map_sub,
    sub_eq_zero]

private theorem span_eq_top_of_subset (hP : affineSpan ℝ P = ⊤) {S : Flat d}
    (h : P ⊆ S) : S = ⊤ := top_unique (hP ▸ affineSpan_le.2 h)

/-- Extend the flat spanned by `Q` to a spanned hyperplane while avoiding `z`. At each step,
choose the next point outside the joint span of the current flat and `z`. -/
private theorem exists_spanned_separating (hP : affineSpan ℝ P = ⊤)
    (Q : Set (Point d)) (hQ : Q ⊆ P) (hne : Q.Nonempty) (z : Point d)
    (hz : z ∉ affineSpan ℝ Q) :
    ∃ H : ITSP.SpannedHyperplaneSet d P, affineSpan ℝ Q ≤ H.val ∧ z ∉ H.val := by
  classical
  let S := affineSpan ℝ Q
  have hS : (S : Set (Point d)).Nonempty := hne.mono (subset_affineSpan ℝ Q)
  change z ∉ S at hz
  have hlt : dim S < d := by
    apply lt_of_lt_of_eq (dim_lt _ hS) (dim_top (d := d))
    exact lt_top_iff_ne_top.mpr fun hh ↦ hz (hh ▸ mem_top ℝ _ z)
  by_cases h : dim S + 1 = d
  · exact ⟨⟨S, isHyperplane_of_dim hS h, Q, hQ, rfl⟩, le_rfl, hz⟩
  have hd := dim_extend hS hz
  have hx : ¬ P ⊆ extendFlat S z := fun hs ↦ by
    rw [span_eq_top_of_subset hP hs, dim_top] at hd
    omega
  obtain ⟨x, hxP, hx⟩ := Set.not_subset.mp hx
  have hxS : x ∉ S := fun hh ↦ hx (le_extend S z hh)
  have hz' : z ∉ extendFlat S x := fun hh ↦
    hx (extend_eq hS hxS hz hh ▸ mem_extend S x)
  have he : extendFlat S x = affineSpan ℝ (insert x Q) := affineSpan_insert_affineSpan ..
  obtain ⟨H, hH, hzH⟩ := exists_spanned_separating hP (insert x Q)
    (Set.insert_subset hxP hQ) (Set.insert_nonempty ..) z (he ▸ hz')
  exact ⟨H, (le_extend S x).trans (he ▸ hH), hzH⟩
termination_by d - dim (affineSpan ℝ Q)
decreasing_by
  rw [← he, dim_extend hS hxS]
  change d - (dim S + 1) < d - dim S
  omega

private noncomputable def weight {A : Type*} [Fintype A] (a : A → Point d) (w : A → ℝ)
    (S : Flat d) : ℝ := by
  classical exact ∑ i, if a i ∈ S then w i else 0

/-- A flat of positive weight lies in an extension of positive weight whenever the total weight is
nonnegative. The one-point extensions count every point outside the flat once, and every point
inside it once per extension. Iterate until the extension is a hyperplane. -/
private theorem positive_hyperplane [Finite P] {A : Type*} [Fintype A]
    (a : A → Point d) (ha : ∀ i, a i ∈ P) (w : A → ℝ) (ht : 0 ≤ ∑ i, w i) (hP : affineSpan ℝ P = ⊤)
    (Q : Set (Point d)) (hQ : Q ⊆ P) (hne : Q.Nonempty)
    (hproper : dim (affineSpan ℝ Q) < d) (hw : 0 < weight a w (affineSpan ℝ Q)) :
    ∃ H : ITSP.SpannedHyperplaneSet d P, 0 < weight a w H.val := by
  classical
  let := Fintype.ofFinite P
  let S := affineSpan ℝ Q
  have hS : (S : Set (Point d)).Nonempty := hne.mono (subset_affineSpan ℝ Q)
  by_cases h : dim S + 1 = d
  · exact ⟨⟨S, isHyperplane_of_dim hS h, Q, hQ, rfl⟩, hw⟩
  let O := Finset.univ.filter (fun x : P ↦ x.val ∉ S)
  let E := O.image fun x ↦ extendFlat S x.val
  have hmem (x : P) (hx : x.val ∉ S) : extendFlat S x.val ∈ E :=
    Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
  have helim {T : Flat d} (hT : T ∈ E) : ∃ x : P, x.val ∉ S ∧ extendFlat S x.val = T := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hT
    exact ⟨x, (Finset.mem_filter.mp hx).2, rfl⟩
  have outside {T : Flat d} (hd : dim T < d) : ∃ x : P, x.val ∉ T := by
    by_contra! hh
    have he := span_eq_top_of_subset hP (fun x hx ↦ hh ⟨x, hx⟩)
    rw [he, dim_top] at hd
    exact hd.false
  obtain ⟨x, hx⟩ := outside hproper
  have dx := dim_extend hS hx
  change dim S < d at hproper
  have dx' : dim (extendFlat S x.val) < d := by omega
  obtain ⟨y, hy⟩ := outside dx'
  have hyS : y.val ∉ S := fun hh ↦ hy (le_extend S _ hh)
  have hcard : 1 < E.card := Finset.one_lt_card.mpr
    ⟨_, hmem x hx, _, hmem y hyS, fun he ↦ hy (he ▸ mem_extend S _)⟩
  have fan (i : A) (hi : a i ∈ P) :
      ∑ T ∈ E, (if a i ∈ T then w i else 0) =
        ((E.card : ℝ) - 1) * (if a i ∈ S then w i else 0) + w i := by
    by_cases hv : a i ∈ S
    · have hall T (hT : T ∈ E) : a i ∈ T := by
        obtain ⟨v, _, rfl⟩ := helim hT
        exact le_extend S _ hv
      rw [Finset.sum_congr rfl (fun T hT ↦ ite_eq_left (hall T hT)), ite_eq_left hv]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    · have htest (T) (hT : T ∈ E) : a i ∈ T ↔ extendFlat S (a i) = T := by
        obtain ⟨v, hv', rfl⟩ := helim hT
        exact ⟨extend_eq hS hv' hv, fun he ↦ he ▸ mem_extend S _⟩
      have he := hmem (⟨a i, hi⟩ : P) hv
      rw [Finset.sum_congr rfl (fun T hT ↦ if_congr (htest T hT) rfl rfl)]
      simp [hv, he]
  have hsum : 0 < ∑ T ∈ E, weight a w T := by
    simp only [weight]
    rw [Finset.sum_comm]
    simp_rw [fan _ (ha _)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    apply add_pos_of_pos_of_nonneg _ ht
    apply mul_pos _ hw
    exact sub_pos.mpr (by exact_mod_cast hcard)
  obtain ⟨T, hT, hpos⟩ : ∃ T ∈ E, 0 < weight a w T := by
    by_contra! hnot
    exact hsum.not_ge (Finset.sum_nonpos hnot)
  obtain ⟨v, hv, rfl⟩ := helim hT
  have he : extendFlat S v.val = affineSpan ℝ (insert v.val Q) := affineSpan_insert_affineSpan ..
  refine positive_hyperplane a ha w ht hP (insert v.val Q) (Set.insert_subset v.property hQ)
    (Set.insert_nonempty ..) ?_ (he ▸ hpos)
  rw [← he, dim_extend hS hv]
  omega
termination_by d - dim (affineSpan ℝ Q)
decreasing_by
  rw [← he, dim_extend hS hv]
  change d - (dim S + 1) < d - dim S
  omega

private abbrev Hyper (P : Set (Point d)) := ↥(ITSP.SpannedHyperplaneSet d P)
private abbrev Matching (P : Set (Point d)) :=
  ∃ f : P → Hyper P, Function.Injective f ∧ ∀ p, p.val ∈ (f p).val

private abbrev flatOf (P : Set (Point d)) (t : Finset P) :=
  affineSpan ℝ (Subtype.val '' (t : Set P))

private theorem finite_generators {Q : Set (Point d)} (h : Q ⊆ P) :
    ∃ t : Finset P, flatOf P t = affineSpan ℝ Q := by
  classical
  obtain ⟨T, hT, he, hi⟩ := exists_affineIndependent ℝ (Point d) Q
  have : Finite T := (finiteDimensional_iff_finite ℝ hi).mp inferInstance
  let := Fintype.ofFinite T
  let j : T → P := fun x ↦ ⟨x.val, h (hT x.property)⟩
  refine ⟨Finset.univ.image j, ?_⟩
  unfold flatOf
  rw [Finset.coe_image, Finset.coe_univ, Set.image_image]
  change affineSpan ℝ ((Subtype.val : T → Point d) '' Set.univ) = _
  rwa [Set.image_univ, Subtype.range_coe]

private theorem hyper_generators (H : Hyper P) : ∃ t : Finset P, flatOf P t = H.val := by
  obtain ⟨Q, hQ, he⟩ := H.property.2
  rw [← he]
  exact finite_generators hQ

private theorem hyper_card : #(Hyper P) ≤ #(Finset P) := by
  choose t ht using (hyper_generators (P := P))
  apply mk_le_of_injective (f := t)
  exact fun H K he ↦ Subtype.ext ((ht H).symm.trans ((congrArg (flatOf P) he).trans (ht K)))

/-- For each subset of points, send real weights on the subset to their sums on all incident
hyperplanes. A nonzero weight vector, after a choice of sign, has nonnegative total and a
positive singleton. The preceding extension argument detects it on some hyperplane, so this
linear map is injective. Comparing dimensions gives Hall’s inequality. -/
private theorem finite_matching [Finite P] (hd : 1 ≤ d) (hP : affineSpan ℝ P = ⊤) : Matching P := by
  classical
  let := Fintype.ofFinite P
  have : Finite (Hyper P) := Cardinal.lt_aleph0_iff_finite.mp
    (lt_of_le_of_lt hyper_card (Cardinal.lt_aleph0_of_finite _))
  let := Fintype.ofFinite (Hyper P)
  apply (Fintype.all_card_le_filter_rel_iff_exists_injective
    (fun (x : P) (H : Hyper P) ↦ x.val ∈ H.val)).mp
  intro B
  let N := Finset.univ.filter fun H : Hyper P ↦ ∃ x ∈ B, x.val ∈ H.val
  let a := fun i : B ↦ i.val.val
  have ha (i : B) : a i ∈ P := i.val.property
  have hai : Function.Injective a := Subtype.val_injective.comp Subtype.val_injective
  let L : (B → ℝ) →ₗ[ℝ] (N → ℝ) :=
    { toFun := fun w H ↦ weight a w H.val.val
      map_add' := by
        intro f g
        ext H
        simp only [weight, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> simp
      map_smul' := by
        intro r f
        ext H
        simp only [weight, Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> simp }
  have cannot (w : B → ℝ) (hw : w ≠ 0) (ht : 0 ≤ ∑ i, w i) (hz : L w = 0) : False := by
    obtain ⟨i, hi⟩ : ∃ i, 0 < w i := by
      by_contra! hle
      have he : ∑ i, w i = 0 := le_antisymm (Finset.sum_nonpos fun i _ ↦ hle i) ht
      exact hw (funext fun i ↦ (Finset.sum_eq_zero_iff_of_nonpos (fun j _ ↦ hle j)).mp he i
        (Finset.mem_univ _))
    have hs : weight a w (affineSpan ℝ {a i}) = w i := by
      simp [weight, affineSpan_singleton, AffineSubspace.mem_singleton_iff, hai.eq_iff]
    obtain ⟨H, hH⟩ := positive_hyperplane a ha w ht hP {a i} (Set.singleton_subset_iff.mpr (ha i))
      (Set.singleton_nonempty _) (by
        rw [dim, affineSpan_singleton, direction_singleton, finrank_bot]
        exact hd)
      (hs ▸ hi)
    have hn : H ∈ N := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra! hnone
      have he : weight a w H.val = 0 := by simp [weight, a, fun i : B ↦ hnone i.val i.property]
      exact hH.ne' he
    exact hH.ne' (congrFun hz ⟨H, hn⟩)
  have hinj : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    by_contra hn
    rcases le_total 0 (∑ i, w i) with ht | ht
    · exact cannot w hn ht hw
    · apply cannot (-w) (neg_ne_zero.mpr hn) _ (by simp [hw])
      simpa using ht
  change B.card ≤ N.card
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
    L.finrank_le_finrank_of_injective hinj

/-- Reserve one value for `e`. In an initial well-order of the domain, each point has fewer
predecessors than available values, even after accounting for the reserved value. -/
private theorem greedy_except {A B : Type} [Infinite A] (R : A → Set B) (e : A)
    (be : B) (hbe : be ∈ R e) (hbig : ∀ x ≠ e, #A ≤ #(R x)) :
    ∃ f : A → B, Function.Injective f ∧ ∀ x, f x ∈ R x := by
  classical
  obtain ⟨lo, wf, horder⟩ := Cardinal.exists_ord_eq_type_lt A
  let step (x : A) (g : Iio x → B) : ∃ b ∈ R x, x = e ∨ (b ≠ be ∧ b ∉ range g) := by
    by_cases hx : x = e
    · exact ⟨be, hx ▸ hbe, Or.inl hx⟩
    have hsmall : #(insert be (range g) : Set B) < #A := by
      rw [Set.insert_eq]
      apply lt_of_le_of_lt (mk_union_le _ _) (add_lt_of_lt (aleph0_le_mk A) ?_ ?_)
      · simpa using one_lt_aleph0.trans_le (aleph0_le_mk A)
      · exact lt_of_le_of_lt (mk_range_le (f := g)) (mk_Iio_lt x horder)
    obtain ⟨b, hb, h⟩ := Set.not_subset.mp (fun sub ↦
      (not_le_of_gt hsmall) ((hbig x hx).trans (mk_le_mk_of_subset sub)))
    exact ⟨b, hb, Or.inr ⟨fun he ↦ h (Set.mem_insert_iff.mpr (Or.inl he)),
      fun hr ↦ h (Set.mem_insert_of_mem _ hr)⟩⟩
  let G (x : A) (g : ∀ y, y < x → B) :=
    if x = e then be else (step x fun i ↦ g i.val i.property).choose
  let f := wf.fix G
  have eqn (x : A) : f x = G x (fun y _ ↦ f y) := wf.fix_eq G x
  have hfe : f e = be := by
    rw [eqn e]
    exact ite_eq_left rfl
  have spec (x : A) (hx : x ≠ e) : f x ∈ R x ∧ f x ≠ be ∧ ∀ y < x, f x ≠ f y := by
    have hh := (step x (fun i ↦ f i.val)).choose_spec
    have hn := hh.2.resolve_left hx
    have he : f x = (step x (fun i ↦ f i.val)).choose := by
      rw [eqn x]
      exact ite_eq_right hx
    exact ⟨he ▸ hh.1, he ▸ hn.1, fun y hy hh' ↦ hn.2 ⟨⟨y, hy⟩, hh'.symm.trans he⟩⟩
  refine ⟨f, fun x y hxy ↦ ?_, fun x ↦ ?_⟩
  · by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · by_cases hy : y = e
      · exact (spec x (hy ▸ hn)).2.1 (hxy.trans (hy ▸ hfe))
      · exact (spec y hy).2.2 x h hxy.symm
    · by_cases hx : x = e
      · exact (spec y (hx ▸ Ne.symm hn)).2.1 (hxy.symm.trans (hx ▸ hfe))
      · exact (spec x hx).2.2 y h hxy
  · by_cases hx : x = e
    · simpa only [hx, hfe] using hbe
    · exact (spec x hx).1

/-- If the flats through a point separate it from every other point, finitely many suffice.
Each necessary intersection strictly lowers the dimension. -/
private theorem finite_cut {I : Type} (F : I → Flat d) (x : Point d)
    (sep : ∀ y ≠ x, ∃ i, x ∈ F i ∧ y ∉ F i) (T : Flat d) (hx : x ∈ T) :
    ∃ s : Finset I, (∀ i ∈ s, x ∈ F i) ∧ ∀ y ∈ T, (∀ i ∈ s, y ∈ F i) → y = x := by
  classical
  by_cases h : ∀ y ∈ T, y = x
  · exact ⟨∅, by simp, fun y hy _ ↦ h y hy⟩
  push Not at h
  obtain ⟨y, hy, hyx⟩ := h
  obtain ⟨i, hix, hiy⟩ := sep y hyx
  have hi : T ⊓ F i < T :=
    lt_of_le_of_ne inf_le_left fun he ↦ hiy ((show y ∈ T ⊓ F i by rwa [he]).2)
  obtain ⟨s, hs, hcut⟩ := finite_cut F x sep (T ⊓ F i) ⟨hx, hix⟩
  refine ⟨insert i s, ?_, ?_⟩
  · simpa [Finset.forall_mem_insert] using And.intro hix hs
  · intro z hz hz'
    exact hcut z ⟨hz, hz' i (Finset.mem_insert_self ..)⟩ fun j hj ↦
      hz' j (Finset.mem_insert_of_mem hj)
termination_by dim T
decreasing_by exact dim_lt hi ⟨x, hx, hix⟩

private abbrev incident (p : P) : Set (Hyper P) := {H | p.val ∈ H.val}

private theorem finset_small {A : Type} {κ : Cardinal} (hκ : ℵ₀ ≤ κ) (h : #A < κ) :
    #(Finset A) < κ := by
  cases finite_or_infinite A with
  | inl hf =>
    let := Fintype.ofFinite A
    exact (lt_aleph0_of_finite _).trans_le hκ
  | inr hi => rwa [mk_finset_of_infinite]

/-- A point `x` outside the line `pq` is the unique intersection of the lines `px` and `qx`.
Spanned hyperplanes through these lines therefore separate `x` from every other point.
Encode `x` by finitely many hyperplanes incident to `p` or `q`. -/
private theorem complement_small [Infinite P] (hP : affineSpan ℝ P = ⊤)
    (p q : P) (hpq : p ≠ q) (hp : #(incident p) < #P) (hq : #(incident q) < #P) :
    #(P \ (affineSpan ℝ {p.val, q.val} : Flat d).carrier : Set (Point d)) < #P := by
  classical
  let L := affineSpan ℝ {p.val, q.val}
  let I := incident p ⊕ incident q
  let F : I → Flat d := Sum.elim (fun h ↦ h.val.val) (fun h ↦ h.val.val)
  have encode (x : ↥(P \ L.carrier : Set (Point d))) : ∃ s : Finset I, (∀ i ∈ s, x.val ∈ F i) ∧
      ∀ y : Point d, (∀ i ∈ s, y ∈ F i) → y = x.val := by
    have sep (y : Point d) (hy : y ≠ x.val) : ∃ i, x.val ∈ F i ∧ y ∉ F i := by
      have aux (a : P) (hn : y ∉ affineSpan ℝ {a.val, x.val}) :
          ∃ H : incident a, x.val ∈ H.val.val ∧ y ∉ H.val.val := by
        obtain ⟨H, hH, hyH⟩ := exists_spanned_separating hP {a.val, x.val}
          (Set.insert_subset a.property (Set.singleton_subset_iff.mpr x.property.1))
          (Set.insert_nonempty ..) y hn
        exact ⟨⟨H, hH (left_mem_affineSpan_pair ..)⟩, hH (right_mem_affineSpan_pair ..), hyH⟩
      by_cases hpy : y ∈ affineSpan ℝ {p.val, x.val}
      · have hqy : y ∉ affineSpan ℝ {q.val, x.val} := by
          intro hqy
          have he := (affineSpan_pair_eq_of_left_mem_of_ne hpy hy).symm.trans
            (affineSpan_pair_eq_of_left_mem_of_ne hqy hy)
          have hh := affineSpan_pair_eq_of_mem_of_mem_of_ne (left_mem_affineSpan_pair ℝ p.val x.val)
            (he ▸ left_mem_affineSpan_pair ℝ q.val x.val) (Subtype.val_injective.ne hpq)
          apply x.property.2
          change x.val ∈ affineSpan ℝ {p.val, q.val}
          rw [hh]
          exact right_mem_affineSpan_pair ..
        obtain ⟨H, hx, hy⟩ := aux q hqy
        exact ⟨Sum.inr H, hx, hy⟩
      · obtain ⟨H, hx, hy⟩ := aux p hpy
        exact ⟨Sum.inl H, hx, hy⟩
    obtain ⟨s, hs, hc⟩ := finite_cut F x.val sep ⊤ (mem_top ℝ _ _)
    exact ⟨s, hs, fun y ↦ hc y (mem_top ℝ _ _)⟩
  choose s hs hcut using encode
  refine lt_of_le_of_lt (mk_le_of_injective (f := s) ?_) (finset_small (aleph0_le_mk P) ?_)
  · intro x y he
    exact Subtype.ext (hcut y x.val (he ▸ hs x))
  · change #((incident p) ⊕ (incident q)) < #P
    simpa only [mk_sum, lift_id] using add_lt_of_lt (aleph0_le_mk P) hp hq

private theorem unique_intersection {p q x y : Point d} {H : Flat d}
    (hx : x ∈ affineSpan ℝ {p, q}) (hy : y ∈ affineSpan ℝ {p, q})
    (hxH : x ∈ H) (hyH : y ∈ H) (h : ¬ affineSpan ℝ {p, q} ≤ H) : x = y := by
  by_contra hne
  exact h ((affineSpan_pair_eq_of_mem_of_mem_of_ne hx hy hne) ▸
    affineSpan_pair_le_of_mem_of_mem hxH hyH)

/-- Retain the points outside the line, its two generators, and every point where a hyperplane
spanned outside the line meets it in a singleton. They form a smaller spanning set. A hyperplane
through any remaining point that avoids the whole line is fresh for the smaller matching and
meets the line only at its assigned point. -/
private theorem line_reduction [Infinite P] (hP : affineSpan ℝ P = ⊤) (p q : P)
    (hsmall : #(P \ (affineSpan ℝ {p.val, q.val} : Flat d).carrier : Set (Point d)) < #P)
    (ih : ∀ P' : Set (Point d), #P' < #P → affineSpan ℝ P' = ⊤ → Matching P') : Matching P := by
  classical
  let L := affineSpan ℝ {p.val, q.val}
  let B := P \ L.carrier
  let C : Set (Point d) := {x | x ∈ P ∧ x ∈ L ∧ ∃ H : Hyper B, x ∈ H.val ∧ ¬ L ≤ H.val}
  have cc : #C ≤ #(Hyper B) := by
    have ch (x : C) := x.property.2.2
    choose H hxH hLH using ch
    apply mk_le_of_injective (f := H)
    intro x y he
    exact Subtype.ext (unique_intersection x.property.2.1 y.property.2.1 (hxH x) (he ▸ hxH y)
      (hLH x))
  have hκ := aleph0_le_mk P
  have cb : #C < #P := cc.trans_lt (hyper_card.trans_lt (finset_small hκ hsmall))
  let U := insert p.val (insert q.val (B ∪ C))
  have bu : B ⊆ U := fun _ hx ↦ Or.inr (Or.inr (Or.inl hx))
  have cu : C ⊆ U := fun _ hx ↦ Or.inr (Or.inr (Or.inr hx))
  have pu : p.val ∈ U := Or.inl rfl
  have qu : q.val ∈ U := Or.inr (Or.inl rfl)
  have us : #U < #P := by
    apply mk_insert_le.trans_lt (add_one_lt_of_lt hκ ?_)
    apply mk_insert_le.trans_lt (add_one_lt_of_lt hκ ?_)
    exact (mk_union_le _ _).trans_lt (add_lt_of_lt hκ hsmall cb)
  have up : U ⊆ P := by
    refine Set.insert_subset p.property (Set.insert_subset q.property (Set.union_subset ?_ ?_))
    · exact Set.sdiff_subset
    · exact fun _ hx ↦ hx.1
  have outside (x : P) (hx : x.val ∉ U) : x.val ∈ L :=
    by_contra fun hn ↦ hx (bu ⟨x.property, hn⟩)
  have hL : L ≤ affineSpan ℝ U :=
    affineSpan_pair_le_of_mem_of_mem (mem_affineSpan ℝ pu) (mem_affineSpan ℝ qu)
  have ut : affineSpan ℝ U = ⊤ := by
    apply span_eq_top_of_subset hP
    intro x hx
    by_cases hu : x ∈ U
    · exact mem_affineSpan ℝ hu
    · exact hL (outside ⟨x, hx⟩ hu)
  obtain ⟨g, hg, hinc⟩ := ih U us ut
  have old (H : Hyper U) : H.val ∈ ITSP.SpannedHyperplaneSet d P := by
    obtain ⟨Q, hQ, he⟩ := H.property.2
    exact ⟨H.property.1, Q, hQ.trans up, he⟩
  have fresh (x : P) (hx : x.val ∉ U) (H : Hyper U) (hn : ¬ L ≤ H.val) : x.val ∉ H.val := by
    intro hxH
    obtain ⟨Q, hQ, he⟩ := H.property.2
    have qb : Q ⊆ B := by
      intro y hy
      refine ⟨up (hQ hy), fun hyl ↦ ?_⟩
      have hye : y ∈ H.val := he ▸ mem_affineSpan ℝ hy
      exact hx (unique_intersection hyl (outside x hx) hye hxH hn ▸ hQ hy)
    exact hx (cu ⟨x.property, outside x hx, ⟨H.val, H.property.1, Q, qb, he⟩, hxH, hn⟩)
  have atPoint (x : P) : ∃ H : Hyper P, x.val ∈ H.val ∧
      (∀ hx : x.val ∈ U, H.val = (g ⟨x.val, hx⟩).val) ∧ (x.val ∉ U → ¬ L ≤ H.val) := by
    by_cases hx : x.val ∈ U
    · exact ⟨⟨_, old (g ⟨_, hx⟩)⟩, hinc ⟨_, hx⟩, fun _ ↦ rfl, fun hn ↦ (hn hx).elim⟩
    · have hn : p.val ∉ affineSpan ℝ {x.val} := by
        rw [affineSpan_singleton, AffineSubspace.mem_singleton_iff]
        intro he
        exact hx (he ▸ pu)
      obtain ⟨H, hH, hpH⟩ := exists_spanned_separating hP {x.val}
        (Set.singleton_subset_iff.mpr x.property) (Set.singleton_nonempty _) p.val hn
      exact ⟨H, hH (mem_affineSpan ℝ (Set.mem_singleton _)), fun hu ↦ (hx hu).elim,
        fun _ h ↦ hpH (h (left_mem_affineSpan_pair ..))⟩
  choose f hf hfo hfn using atPoint
  have distinct (x y : P) (hx : x.val ∈ U) (hy : y.val ∉ U) : f x ≠ f y := by
    intro he
    have eqv : (f y).val = (g ⟨x.val, hx⟩).val := he ▸ hfo x hx
    exact fresh y hy (g ⟨_, hx⟩) (eqv ▸ hfn y hy) (eqv ▸ hf y)
  refine ⟨f, fun x y he ↦ ?_, hf⟩
  by_cases hx : x.val ∈ U <;> by_cases hy : y.val ∈ U
  · have eqv := (hfo x hx).symm.trans ((congrArg Subtype.val he).trans (hfo y hy))
    exact Subtype.ext (congrArg (Subtype.val : U → Point d) (hg (Subtype.ext eqv)))
  · exact (distinct x y hx hy he).elim
  · exact (distinct y x hy hx he.symm).elim
  · exact Subtype.ext (unique_intersection (outside x hx) (outside y hy) (hf x) (he ▸ hf y)
      (hfn x hx))

private theorem matching (hd : 1 ≤ d) (P : Set (Point d)) (hP : affineSpan ℝ P = ⊤) :
    Matching P := by
  classical
  cases finite_or_infinite P with
  | inl hfin => exact finite_matching hd hP
  | inr hinf =>
    by_cases hbad : ∃ p q : P, p ≠ q ∧ #(incident p) < #P ∧ #(incident q) < #P
    · obtain ⟨p, q, hpq, hp, hq⟩ := hbad
      exact line_reduction hP p q (complement_small hP p q hpq hp hq)
        (fun U _ hu ↦ matching hd U hu)
    obtain ⟨e, he⟩ : ∃ e : P, ∀ x ≠ e, #P ≤ #(incident x) := by
      by_cases hb : ∃ e : P, #(incident e) < #P
      · obtain ⟨e, he⟩ := hb
        exact ⟨e, fun x hx ↦ le_of_not_gt fun hh ↦ hbad ⟨e, x, hx.symm, he, hh⟩⟩
      · push Not at hb
        exact ⟨Classical.arbitrary P, fun x _ ↦ hb x⟩
    obtain ⟨z, hz⟩ := exists_ne e
    have hn : z.val ∉ affineSpan ℝ {e.val} := by
      rw [affineSpan_singleton, AffineSubspace.mem_singleton_iff]
      exact Subtype.val_injective.ne hz
    obtain ⟨H, hH, _⟩ := exists_spanned_separating hP {e.val}
      (Set.singleton_subset_iff.mpr e.property) (Set.singleton_nonempty _) z.val hn
    exact greedy_except incident e H (hH (mem_affineSpan ℝ (Set.mem_singleton _))) he
termination_by #P

/--
**Spanning point sets have injective point-to-hyperplane matchings.** For every $d \ge 1$ and
every set $P \subseteq \mathbb{R}^d$ whose affine span is all of $\mathbb{R}^d$, let $\mathcal{H}$
be the set of affine hyperplanes of $\mathbb{R}^d$ that equal the affine span of some subset of
$P$. Then there is an injective map $f \colon P \to \mathcal{H}$ with $p \in f(p)$ for every
$p \in P$.

This answers the question of `OWR-1183-011` affirmatively. It follows from Farley's Theorem 11:
every geometric lattice of finite rank greater than $1$, of any cardinality, has an injective
map sending each atom to a coatom containing it; apply it to the lattice of affine flats
spanned by subsets of $P$.

Source: J. D. Farley, A question of Björner from 1981:
infinite geometric lattices of finite rank have matchings, Australasian Journal of Combinatorics
82 (2022) 228-235, arXiv:2004.11972, https://arxiv.org/abs/2004.11972. Moved from
`OpenConjectures/Geometry/InfiniteTransversalsSpannedHyperplanes`.
-/
public theorem OWR1183Question_holds : ITSP.OWR1183Question :=
  fun d hd P hP ↦ matching (d := d) hd P hP

end MathlibExt.Geometry.InfiniteTransversalsSpannedHyperplanesWanted
