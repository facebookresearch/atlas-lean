/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The five-color theorem for straight-line planar graphs

We follow Heawood's deletion and recoloring argument (Bondy and Murty,
*Graph Theory*, §11.2, Theorem 11.6). We obtain the low-degree vertex directly
from a horizontal sweep: each gap between consecutive rightward edges is
charged to the first vertex between them. At most two gaps charge any vertex.

For the degree-five step we use a signed vertical ray count, not a general
Jordan curve theorem. Along a segment disjoint from a closed walk, the
changes in the ray count telescope. Applied to a bichromatic walk closed
through the deleted vertex, this prevents a second bichromatic walk from
joining the two alternating spokes.
-/

open SimpleGraph
open scoped BigOperators

namespace MetaMathlibExt

namespace FiveColor

/-! ### Finite recoloring -/

section

/-- Planarity restricts along any injective graph homomorphism. -/
theorem planar_of_injective_hom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : H.IsPlanar) (φ : G →g H) (hφ : Function.Injective φ) : G.IsPlanar := by
  rcases h with he | ⟨f, hf, hne, hc⟩
  · exact Or.inl fun hv ↦ he (hv.map φ)
  · refine Or.inr ⟨f ∘ φ, hf.comp hφ, ?_, ?_⟩
    · intro a b ha
      exact hne (φ.map_rel ha)
    · intro a b c d hab hcd hp
      apply hc (φ.map_rel hab) (φ.map_rel hcd)
      intro he
      apply hp
      ext i
      have hi : φ i ∈ ({φ a, φ b} : Set W) ↔ φ i ∈ ({φ c, φ d} : Set W) := by rw [he]
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, hφ.eq_iff] using hi

/-- Vertices surviving deletion. -/
abbrev Away {V : Type*} (v : V) := {w : V // w ≠ v}

/-- Induced graph on vertices surviving deletion. -/
abbrev deleted {V : Type*} (G : SimpleGraph V) (v : V) := G.induce {w | w ≠ v}

/-- A neighbor survives deletion by irreflexivity. -/
def restrictNeighbor {V : Type*} {G : SimpleGraph V} {v : V}
    (w : G.neighborSet v) : Away v := ⟨w, G.ne_of_adj w.prop |>.symm⟩

private theorem planar_deleted {V : Type*} {G : SimpleGraph V} (h : G.IsPlanar) (v : V) :
    (deleted G v).IsPlanar :=
  planar_of_injective_hom h ⟨Subtype.val, fun ha ↦ ha⟩ Subtype.val_injective

/-- Keep only the edges with both ends in the indicated pair of color classes. -/
def kempe {V K : Type*} {H : SimpleGraph V} (C : H.Coloring K) (i j : K) : SimpleGraph V where
  Adj a b := H.Adj a b ∧ (C a = i ∨ C a = j) ∧ (C b = i ∨ C b = j)
  symm := ⟨fun _ _ h ↦ ⟨Adj.symm (G := H) h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h ↦ H.irrefl h.1⟩

/-- Swapping the two colors on one component of the bichromatic graph preserves properness. -/
noncomputable def swapComponent {V K : Type*} [DecidableEq K] {H : SimpleGraph V}
    (C : H.Coloring K) (i j : K) (r : V) : H.Coloring K := by
  classical
  let H' := kempe C i j
  let σ := Equiv.swap i j
  refine Coloring.mk (fun x ↦ if H'.Reachable r x then σ (C x) else C x) ?_
  intro a b hab
  have mix : ∀ {x y}, H.Adj x y → H'.Reachable r x → ¬H'.Reachable r y → σ (C x) ≠ C y := by
    intro x y hxy hx hy he
    have hy' : C y ≠ i ∧ C y ≠ j := by
      by_contra hf
      have hf' : C y = i ∨ C y = j := by tauto
      have hx' : C x = i ∨ C x = j := by
        rcases hf' with hi | hj
        · rw [hi, ← Equiv.swap_apply_right i j] at he
          exact Or.inr (σ.injective he)
        · rw [hj, ← Equiv.swap_apply_left i j] at he
          exact Or.inl (σ.injective he)
      exact hy (hx.trans (Adj.reachable (G := H') ⟨hxy, hx', hf'⟩))
    apply C.valid hxy
    apply σ.injective
    rw [he]
    exact (Equiv.swap_apply_of_ne_of_ne hy'.1 hy'.2).symm
  by_cases ha : H'.Reachable r a <;> by_cases hb : H'.Reachable r b
  · simpa only [ite_eq_left ha, ite_eq_left hb, σ.injective.ne_iff] using C.valid hab
  · simpa only [ite_eq_left ha, ite_eq_right hb] using mix hab ha hb
  · simpa only [ite_eq_right ha, ite_eq_left hb] using (mix hab.symm hb ha).symm
  · simpa only [ite_eq_right ha, ite_eq_right hb] using C.valid hab

private theorem swapComponent_apply_of_reachable {V K : Type*} [DecidableEq K] {H : SimpleGraph V}
    (C : H.Coloring K) {i j : K} {r x : V} (h : (kempe C i j).Reachable r x) :
    swapComponent C i j r x = (Equiv.swap i j) (C x) := by
  classical
  change (if (kempe C i j).Reachable r x then _ else _) = _
  rw [ite_eq_left h]

private theorem swapComponent_apply_of_not_reachable {V K : Type*} [DecidableEq K]
    {H : SimpleGraph V} (C : H.Coloring K) {i j : K} {r x : V}
    (h : ¬(kempe C i j).Reachable r x) :
    swapComponent C i j r x = C x := by
  classical
  change (if (kempe C i j).Reachable r x then _ else _) = _
  rw [ite_eq_right h]

private theorem extend_of_missing {V K : Type*} {G : SimpleGraph V} {v : V}
    (C : (deleted G v).Coloring K) (k : K)
    (hk : ∀ w : G.neighborSet v, C (restrictNeighbor w) ≠ k) : Nonempty (G.Coloring K) := by
  classical
  let col : V → K := fun w ↦ if hw : w ≠ v then C ⟨w, hw⟩ else k
  refine ⟨Coloring.mk col ?_⟩
  intro a b hab
  by_cases ha : a = v
  · subst a
    simp only [col, dite_eq_right (not_not_intro rfl), dite_eq_left (G.ne_of_adj hab).symm]
    exact (hk ⟨b, hab⟩).symm
  by_cases hb : b = v
  · subst b
    simp only [col, dite_eq_right (not_not_intro rfl), dite_eq_left (G.ne_of_adj hab)]
    exact hk ⟨a, hab.symm⟩
  simpa only [col, dite_eq_left ha, dite_eq_left hb]
    using C.valid (v := ⟨a, ha⟩) (w := ⟨b, hb⟩) hab

private theorem extend_of_unjoined_pair {V K : Type*}
    {G : SimpleGraph V} {v : V} (C : (deleted G v).Coloring K)
    (hinj : Function.Injective (fun w : G.neighborSet v ↦ C (restrictNeighbor w)))
    {a b : G.neighborSet v}
    (h : ¬(kempe C (C (restrictNeighbor a)) (C (restrictNeighbor b))).Reachable
      (restrictNeighbor a) (restrictNeighbor b)) : Nonempty (G.Coloring K) := by
  classical
  let i := C (restrictNeighbor a)
  let j := C (restrictNeighbor b)
  let r := restrictNeighbor a
  refine extend_of_missing (swapComponent C i j r) i (fun w ↦ ?_)
  by_cases hr : (kempe C i j).Reachable r (restrictNeighbor w)
  · rw [swapComponent_apply_of_reachable C hr]
    intro he
    have he' := (Equiv.swap i j).injective (he.trans (Equiv.swap_apply_right i j).symm)
    exact h (show (kempe C i j).Reachable r (restrictNeighbor b) from hinj he' ▸ hr)
  · rw [swapComponent_apply_of_not_reachable C hr]
    intro he
    exact hr (show (kempe C i j).Reachable r (restrictNeighbor w) from
      (hinj he).symm ▸ Reachable.refl (G := kempe C i j) r)

/-- The pointwise form of the geometry needed at a degree-five vertex. -/
def LocalKempe {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  ∀ C : (deleted G v).Coloring (Fin 5),
    Function.Bijective (fun w : G.neighborSet v ↦ C (restrictNeighbor w)) →
      ∃ a b : G.neighborSet v, a ≠ b ∧
        ¬(kempe C (C (restrictNeighbor a)) (C (restrictNeighbor b))).Reachable
          (restrictNeighbor a) (restrictNeighbor b)

/-- Heawood's extension step, with the geometric path obstruction isolated. -/
theorem extend_five {V : Type*} [Finite V] {G : SimpleGraph V} {v : V}
    (C : (deleted G v).Coloring (Fin 5)) (hcard : Nat.card (G.neighborSet v) ≤ 5)
    (hK : LocalKempe G v) : Nonempty (G.Coloring (Fin 5)) := by
  classical
  let f := fun w : G.neighborSet v ↦ C (restrictNeighbor w)
  by_cases hsurj : Function.Surjective f
  · let := Fintype.ofFinite (G.neighborSet v)
    have hle : Fintype.card (G.neighborSet v) ≤ Fintype.card (Fin 5) := by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using hcard
    have heq := hle.antisymm (Fintype.card_le_of_surjective f hsurj)
    have hbij := (Fintype.bijective_iff_surjective_and_card f).2 ⟨hsurj, heq⟩
    obtain ⟨a, b, _, hab⟩ := hK C hbij
    exact extend_of_unjoined_pair C hbij.injective hab
  · change ¬∀ k, ∃ w, f w = k at hsurj
    push Not at hsurj
    obtain ⟨k, hk⟩ := hsurj
    exact extend_of_missing C k hk

end

/-! ### Horizontal projection -/

section

/-- The horizontal coordinates are distinct, and edge contacts are only shared endpoints. -/
structure Drawing {V : Type*} (G : SimpleGraph V) where
  point : V → ℝ × ℝ
  xinj : Function.Injective fun v ↦ (point v).1
  meet : ∀ ⦃a b c d⦄, G.Adj a b → G.Adj c d → ({a, b} : Set V) ≠ {c, d} →
    Segment (point a) (point b) ∩ Segment (point c) (point d) ⊆
      ({point a, point b} : Set (ℝ × ℝ)) ∩ {point c, point d}

/-- Horizontal coordinate in a drawing. -/
abbrev Drawing.x {V : Type*} {G : SimpleGraph V} (D : Drawing G) (v : V) : ℝ := (D.point v).1

/-- Vertical coordinate in a drawing. -/
abbrev Drawing.y {V : Type*} {G : SimpleGraph V} (D : Drawing G) (v : V) : ℝ := (D.point v).2

private def shear (k : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1 + k * p.2, p.2)

private theorem shear_inj (k : ℝ) : Function.Injective (shear k) := by
  intro p q h
  have hy := congrArg Prod.snd h
  have hx := congrArg Prod.fst h
  change p.2 = q.2 at hy
  change p.1 + k * p.2 = q.1 + k * q.2 at hx
  rw [hy] at hx
  exact Prod.ext (add_right_cancel hx) hy

private theorem shear_segment (k : ℝ) {a b p : ℝ × ℝ} :
    shear k p ∈ Segment (shear k a) (shear k b) ↔ p ∈ Segment a b := by
  constructor <;> rintro ⟨t, ht0, ht1, hx, hy⟩ <;> refine ⟨t, ht0, ht1, ?_, hy⟩
  · change p.1 + k * p.2 = a.1 + k * a.2 + t * (b.1 + k * b.2 - (a.1 + k * a.2)) at hx
    have hy' : p.2 = a.2 + t * (b.2 - a.2) := hy
    rw [hy'] at hx
    linear_combination hx
  · change p.1 + k * p.2 = a.1 + k * a.2 + t * (b.1 + k * b.2 - (a.1 + k * a.2))
    exact (by rw [hx, hy]; ring)

private theorem shear_surj (k : ℝ) : Function.Surjective (shear k) := by
  intro p
  exact ⟨(p.1 - k * p.2, p.2), Prod.ext (sub_add_cancel _ _) rfl⟩

/-- Any nonempty finite straight-line planar graph has such a drawing. -/
theorem drawing_of_planar {V : Type*} [Finite V] [Nonempty V] {G : SimpleGraph V}
    (hG : G.IsPlanar) : Nonempty (Drawing G) := by
  classical
  rcases hG with h | ⟨f, hf, _, hm⟩
  · exact (h inferInstance).elim
  let : Fintype V := Fintype.ofFinite V
  let bad : V × V → ℝ := fun (u, v) ↦ ((f v).1 - (f u).1) / ((f u).2 - (f v).2)
  let s : Finset ℝ := Finset.univ.image bad
  have hs : s.Nonempty := Finset.univ_nonempty.image _
  let k := s.max' hs + 1
  have hk : k ∉ s := fun hm' ↦ (not_le_of_gt (lt_add_one _) (Finset.le_max' s k hm'))
  refine ⟨⟨shear k ∘ f, ?_, ?_⟩⟩
  · intro u v h
    change (f u).1 + k * (f u).2 = (f v).1 + k * (f v).2 at h
    by_cases hy : (f u).2 = (f v).2
    · rw [hy] at h
      exact hf (Prod.ext (add_right_cancel h) hy)
    · exfalso
      apply hk
      refine Finset.mem_image.mpr ⟨(u, v), Finset.mem_univ _, ?_⟩
      exact (div_eq_iff (sub_ne_zero.mpr hy)).2 (by linear_combination -h)
  · intro a b c d hab hcd hn p hp
    obtain ⟨q, rfl⟩ := shear_surj k p
    have hq := hm hab hcd hn ⟨(shear_segment k).1 hp.1, (shear_segment k).1 hp.2⟩
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Function.comp_apply, (shear_inj k).eq_iff] at hq ⊢
    exact hq

section Lines

variable {V : Type*} {G : SimpleGraph V} (D : Drawing G)

/-- Slope of the line through two drawing vertices. -/
noncomputable def Drawing.slope (a b : V) : ℝ := (D.y b - D.y a) / (D.x b - D.x a)

/-- The height of the affine extension of an edge at horizontal coordinate `t`. -/
noncomputable def Drawing.height (a b : V) (t : ℝ) : ℝ := D.y a + (t - D.x a) * D.slope a b

/-- The affine height at the first endpoint. -/
@[simp] theorem Drawing.height_left (a b : V) : D.height a b (D.x a) = D.y a := by
  simp [Drawing.height]

/-- The affine height at the second endpoint. -/
@[simp] theorem Drawing.height_right {a b : V} (h : a ≠ b) : D.height a b (D.x b) = D.y b := by
  have hn := sub_ne_zero.mpr (D.xinj.ne h.symm)
  unfold Drawing.height Drawing.slope
  rw [mul_div_assoc', mul_comm (D.x b - D.x a), mul_div_cancel_right₀ _ hn]
  ring

/-- Swapping the endpoints does not change the slope. -/
theorem Drawing.slope_symm (a b : V) : D.slope a b = D.slope b a := by
  unfold Drawing.slope
  rw [← neg_sub (D.y b) (D.y a), ← neg_sub (D.x b) (D.x a), neg_div_neg_eq]

/-- Swapping the endpoints does not change the affine height. -/
theorem Drawing.height_symm {a b : V} (h : a ≠ b) (t : ℝ) :
    D.height a b t = D.height b a t := by
  have he := D.height_right h
  unfold Drawing.height at he ⊢
  rw [D.slope_symm a b] at he ⊢
  linear_combination he

/-- The affine height over the closed horizontal interval lies on the closed segment. -/
theorem Drawing.height_mem_segment {a b : V} {t : ℝ} (hab : D.x a < D.x b)
    (ht₁ : D.x a ≤ t) (ht₂ : t ≤ D.x b) :
    (t, D.height a b t) ∈ Segment (D.point a) (D.point b) := by
  have hd : 0 < D.x b - D.x a := sub_pos.mpr hab
  refine ⟨(t - D.x a) / (D.x b - D.x a), div_nonneg (sub_nonneg.mpr ht₁) hd.le,
    (div_le_one hd).2 (sub_le_sub_right ht₂ _), ?_, ?_⟩
  · change t = D.x a + (t - D.x a) / (D.x b - D.x a) * (D.x b - D.x a)
    rw [div_mul_cancel₀ _ hd.ne']
    ring
  · change D.height a b t = D.y a + (t - D.x a) / (D.x b - D.x a) * (D.y b - D.y a)
    unfold Drawing.height Drawing.slope
    rw [div_mul_eq_mul_div, mul_div_assoc']

/-- Edges written from left to right are distinct if their ordered endpoints differ. -/
theorem Drawing.edges_ne {a b c d : V} (hab : D.x a < D.x b) (hcd : D.x c < D.x d)
    (hne : a ≠ c ∨ b ≠ d) : ({a, b} : Set V) ≠ {c, d} := by
  intro he
  have ha : a = c ∨ a = d := by
    simpa only [he, Set.mem_insert_iff, Set.mem_singleton_iff] using
      (show a ∈ ({a, b} : Set V) from Set.mem_insert a _)
  have hb : b = c ∨ b = d := by
    simpa only [he, Set.mem_insert_iff, Set.mem_singleton_iff] using
      (show b ∈ ({a, b} : Set V) from Set.mem_insert_of_mem _ rfl)
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (lt_irrefl _ hab).elim
  · exact hne.elim (fun h ↦ h rfl) (fun h ↦ h rfl)
  · exact (lt_asymm hab hcd).elim
  · exact (lt_irrefl _ hab).elim

/-- Two distinct edges can meet only at a shared vertex, with its horizontal coordinate. -/
theorem Drawing.contact_at_vertex {a b c d : V} {t y : ℝ}
    (hab : G.Adj a b) (hcd : G.Adj c d) (hne : ({a, b} : Set V) ≠ {c, d})
    (h₁ : (t, y) ∈ Segment (D.point a) (D.point b))
    (h₂ : (t, y) ∈ Segment (D.point c) (D.point d)) :
    ∃ v : V, (v = a ∨ v = b) ∧ (v = c ∨ v = d) ∧ D.x v = t := by
  have hp := D.meet hab hcd hne ⟨h₁, h₂⟩
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  have get : ∀ {v : V}, (t, y) = D.point v → t = D.x v := fun h ↦ congrArg Prod.fst h
  rcases hp.1 with ha | hb
  · refine ⟨a, Or.inl rfl, hp.2.imp ?_ ?_, (get ha).symm⟩ <;>
      exact fun h ↦ D.xinj ((get ha).symm.trans (get h))
  · refine ⟨b, Or.inr rfl, hp.2.imp ?_ ?_, (get hb).symm⟩ <;>
      exact fun h ↦ D.xinj ((get hb).symm.trans (get h))

/-- Equal heights on distinct edges can only occur at their common ends. -/
theorem Drawing.height_eq_imp_shared {a b c d : V} {t : ℝ}
    (hab : G.Adj a b) (hcd : G.Adj c d) (habx : D.x a < D.x b) (hcdx : D.x c < D.x d)
    (hne : a ≠ c ∨ b ≠ d) (hta : D.x a ≤ t) (htb : t ≤ D.x b)
    (htc : D.x c ≤ t) (htd : t ≤ D.x d) (ht : D.height a b t = D.height c d t) :
    ∃ v : V, (v = a ∨ v = b) ∧ (v = c ∨ v = d) ∧ D.x v = t :=
  D.contact_at_vertex hab hcd (D.edges_ne habx hcdx hne)
    (D.height_mem_segment habx hta htb) (ht ▸ D.height_mem_segment hcdx htc htd)

/-- An affine function that never vanishes on an interval has constant strict sign there. -/
theorem affine_sign {A B s t : ℝ} (hst : s ≤ t)
    (hne : ∀ z, s ≤ z → z ≤ t → A + z * B ≠ 0) :
    0 < A + s * B ↔ 0 < A + t * B := by
  by_cases hB : B = 0
  · simp only [hB, mul_zero, add_zero]
  have hz : A + (-A / B) * B = 0 := by rw [div_mul_cancel₀ _ hB, add_neg_cancel]
  have eqn (x : ℝ) : A + x * B = (x - -A / B) * B := by
    rw [sub_mul, div_mul_cancel₀ _ hB]
    ring
  rw [eqn, eqn]
  have sides : -A / B < s ∨ t < -A / B := by
    by_contra! hn
    exact hne _ hn.1 hn.2 hz
  rcases sides with hs | ht
  · have hs' := sub_pos.mpr hs
    have ht' := sub_pos.mpr (hs.trans_le hst)
    simp only [mul_pos_iff, hs', ht', true_and, not_lt_of_gt hs', not_lt_of_gt ht', false_and,
      or_false]
  · have ht' := sub_neg.mpr ht
    have hs' := sub_neg.mpr (hst.trans_lt ht)
    simp only [mul_pos_iff, hs', ht', true_and, not_lt_of_gt hs', not_lt_of_gt ht', false_and,
      false_or]

/-- The relative order of affine heights is fixed on any interval without a contact. -/
theorem Drawing.height_lt_iff {a b c d : V} {s t : ℝ} (hst : s ≤ t)
    (hne : ∀ z, s ≤ z → z ≤ t → D.height a b z ≠ D.height c d z) :
    D.height a b s < D.height c d s ↔ D.height a b t < D.height c d t := by
  let A := D.y c - D.x c * D.slope c d - (D.y a - D.x a * D.slope a b)
  let B := D.slope c d - D.slope a b
  have he (z : ℝ) : A + z * B = D.height c d z - D.height a b z := by
    dsimp [A, B, Drawing.height]
    ring
  have hh := affine_sign (A := A) (B := B) hst (by
    intro z hsz hzt
    rw [he]
    exact sub_ne_zero.mpr (Ne.symm (hne z hsz hzt)))
  simpa only [he, sub_pos] using hh

/-- At a slice to the right of a common endpoint, height and slope have the same order. -/
theorem Drawing.height_lt_iff_slope {a b c : V} {t : ℝ} (ht : D.x a < t) :
    D.height a b t < D.height a c t ↔ D.slope a b < D.slope a c := by
  simp only [Drawing.height, add_lt_add_iff_left, mul_lt_mul_iff_right₀ (sub_pos.mpr ht)]

/-- Two different edges extending rightward from the same vertex have different slopes. -/
theorem Drawing.slope_ne {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c)
    (hb : D.x a < D.x b) (hc : D.x a < D.x c) (hne : b ≠ c) :
    D.slope a b ≠ D.slope a c := by
  intro he
  let t := (D.x a + min (D.x b) (D.x c)) / 2
  have hmin := lt_min hb hc
  have ht : D.x a < t := by dsimp [t]; linarith
  have htm : t < min (D.x b) (D.x c) := by dsimp [t]; linarith
  have htb := htm.trans_le (min_le_left (D.x b) (D.x c))
  have htc := htm.trans_le (min_le_right (D.x b) (D.x c))
  have hhh : D.height a b t = D.height a c t := by simp only [Drawing.height, he]
  obtain ⟨w, hw, _, hxt⟩ := D.height_eq_imp_shared hab hac hb hc (Or.inr hne)
    ht.le htb.le ht.le htc.le hhh
  rcases hw with rfl | rfl
  · exact ht.ne hxt
  · exact htb.ne hxt.symm

end Lines

end

/-! ### The low-degree vertex -/

section

variable {V : Type*} {G : SimpleGraph V} (D : Drawing G)

private def RightEdge := {e : G.Dart // D.x e.fst < D.x e.snd}

private instance [Finite V] : Finite (RightEdge D) := by
  let : Fintype V := Fintype.ofFinite V
  classical
  dsimp [RightEdge]
  infer_instance

private noncomputable def orient (e : G.Dart) : RightEdge D × Bool := by
  classical
  exact if h : D.x e.fst < D.x e.snd then (⟨e, h⟩, true)
    else (⟨e.symm, lt_of_le_of_ne (le_of_not_gt h) (D.xinj.ne e.snd_ne_fst)⟩, false)

private theorem orient_injective : Function.Injective (orient D) := by
  classical
  intro a b h
  unfold orient at h
  split at h <;> split at h
  · exact congrArg Subtype.val (Prod.mk.inj h).1
  · exact Bool.noConfusion ((Prod.mk.inj h).2)
  · exact Bool.noConfusion ((Prod.mk.inj h).2)
  · exact Dart.symm_involutive.injective (congrArg Subtype.val (Prod.mk.inj h).1)

private def Above (e : RightEdge D) (c : V) : Prop :=
  G.Adj e.1.fst c ∧ D.x e.1.fst < D.x c ∧ D.slope e.1.fst e.1.snd < D.slope e.1.fst c

private structure Gap (e : RightEdge D) where
  upper : V
  above : Above D e upper
  next : ∀ c, Above D e c → D.slope e.1.fst upper ≤ D.slope e.1.fst c

private noncomputable def nextGap [Fintype V] {e : RightEdge D} (h : ∃ c, Above D e c) :
    Gap D e := by
  classical
  let s := Finset.univ.filter (Above D e)
  have hs : s.Nonempty := by
    obtain ⟨c, hc⟩ := h
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩
  let hm := Finset.exists_min_image s (D.slope e.1.fst) hs
  exact ⟨hm.choose, (Finset.mem_filter.mp hm.choose_spec.1).2,
    fun b hb ↦ hm.choose_spec.2 b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)⟩

private def Stops {e : RightEdge D} (g : Gap D e) (q : V) : Prop :=
  D.x e.1.fst < D.x q ∧ D.x q ≤ D.x e.1.snd ∧ D.x q ≤ D.x g.upper ∧
    D.height e.1.fst e.1.snd (D.x q) ≤ D.y q ∧ D.y q ≤ D.height e.1.fst g.upper (D.x q)

private theorem gap_width {e : RightEdge D} (g : Gap D e) {t : ℝ} (ht : D.x e.1.fst < t) :
    D.height e.1.fst e.1.snd t < D.height e.1.fst g.upper t :=
  (D.height_lt_iff_slope ht).2 g.above.2.2

private theorem gap_has_stop {e : RightEdge D} (g : Gap D e) : ∃ q, Stops D g q := by
  by_cases h : D.x e.1.snd ≤ D.x g.upper
  · refine ⟨e.1.snd, e.2, le_rfl, h, ?_, ?_⟩
    · rw [D.height_right e.1.fst_ne_snd]
    · rw [← D.height_right e.1.fst_ne_snd]
      exact (gap_width D g e.2).le
  · have hx := g.above.2.1
    have hn : e.1.fst ≠ g.upper := ne_of_apply_ne D.x hx.ne
    refine ⟨g.upper, hx, (le_of_not_ge h), le_rfl, ?_, ?_⟩
    · rw [← D.height_right hn]
      exact (gap_width D g hx).le
    · rw [D.height_right hn]

private structure FirstStop {e : RightEdge D} (g : Gap D e) where
  vertex : V
  stops : Stops D g vertex
  first : ∀ q, Stops D g q → D.x vertex ≤ D.x q

private noncomputable def firstStop [Fintype V] {e : RightEdge D} (g : Gap D e) :
    FirstStop D g := by
  classical
  let s := Finset.univ.filter (Stops D g)
  have hs : s.Nonempty := by
    obtain ⟨q, hq⟩ := gap_has_stop D g
    exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩⟩
  let hm := Finset.exists_min_image s D.x hs
  exact ⟨hm.choose, (Finset.mem_filter.mp hm.choose_spec.1).2,
    fun b hb ↦ hm.choose_spec.2 b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)⟩

/-- On the strip between the later origin and the stopping slice, two edges with distinct
origins cannot meet before the stopping slice: the earlier edge is strictly inside its span. -/
private theorem earlier_noncontact {a b c d : V} {t : ℝ} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : D.x a < D.x c) (htc : D.x c < t) (htb : t ≤ D.x b) (htd : t ≤ D.x d)
    (hne : D.height a b t ≠ D.height c d t) :
    ∀ z, D.x c ≤ z → z ≤ t → D.height a b z ≠ D.height c d z := by
  intro z hcz hzt hz
  rcases hzt.eq_or_lt with rfl | hzt
  · exact hne hz
  have ha := hac.trans_le hcz
  have hb := hzt.trans_le htb
  obtain ⟨w, hw, _, hwx⟩ := D.height_eq_imp_shared hab hcd (ha.trans hb)
    (htc.trans_le htd) (Or.inl (ne_of_apply_ne D.x hac.ne)) ha.le hb.le hcz
    (hzt.le.trans htd) hz
  rcases hw with rfl | rfl
  · exact ha.ne hwx
  · exact hb.ne hwx.symm

private theorem not_earlier_gap {e f : RightEdge D} {g : Gap D e} {h : Gap D f}
    (s : FirstStop D g) (t : FirstStop D h) (heq : s.vertex = t.vertex)
    (hearly : D.x e.1.fst < D.x f.1.fst)
    (h₁ : D.height e.1.fst e.1.snd (D.x s.vertex) < D.height f.1.fst h.upper (D.x s.vertex))
    (h₂ : D.height f.1.fst f.1.snd (D.x s.vertex) < D.height e.1.fst g.upper (D.x s.vertex)) :
    False := by
  obtain ⟨_, hsb, hsc, _, _⟩ := s.stops
  obtain ⟨ht₁, ht₂, ht₃, _, _⟩ := t.stops
  rw [← heq] at ht₁ ht₂ ht₃
  have hn₁ := earlier_noncontact D e.1.adj h.above.1 hearly ht₁ hsb ht₃ h₁.ne
  have hn₂ := earlier_noncontact D g.above.1 f.1.adj hearly ht₁ hsc ht₂ h₂.ne.symm
  have hl := (D.height_lt_iff ht₁.le hn₁).2 h₁
  have hr := (D.height_lt_iff ht₁.le (fun z l r ↦ (hn₂ z l r).symm)).2 h₂
  rw [D.height_left] at hl hr
  exact ht₁.not_ge (s.first _ ⟨hearly, ht₁.le.trans hsb, ht₁.le.trans hsc, hl.le, hr.le⟩)

private theorem eq_of_overlap {e f : RightEdge D} {g : Gap D e} {h : Gap D f}
    (s : FirstStop D g) (t : FirstStop D h) (heq : s.vertex = t.vertex)
    (h₁ : D.height e.1.fst e.1.snd (D.x s.vertex) < D.height f.1.fst h.upper (D.x s.vertex))
    (h₂ : D.height f.1.fst f.1.snd (D.x s.vertex) < D.height e.1.fst g.upper (D.x s.vertex)) :
    e = f := by
  have hx : e.1.fst = f.1.fst := by
    rcases lt_trichotomy (D.x e.1.fst) (D.x f.1.fst) with hlt | he | hgt
    · exact (not_earlier_gap D s t heq hlt h₁ h₂).elim
    · exact D.xinj he
    · rw [heq] at h₁ h₂
      exact (not_earlier_gap D t s heq.symm hgt h₂ h₁).elim
  have hts := s.stops.1
  have h₁' : D.slope f.1.fst e.1.snd < D.slope f.1.fst h.upper :=
    (D.height_lt_iff_slope (hx ▸ hts)).1 (hx ▸ h₁)
  have h₂' : D.slope e.1.fst f.1.snd < D.slope e.1.fst g.upper :=
    (D.height_lt_iff_slope hts).1 (hx.symm ▸ h₂)
  have hs : D.slope e.1.fst e.1.snd = D.slope e.1.fst f.1.snd := by
    rcases lt_trichotomy (D.slope e.1.fst e.1.snd) (D.slope e.1.fst f.1.snd) with hl | he | hr
    · have hm := g.next _ ⟨hx.symm ▸ f.1.adj, hx.symm ▸ f.2, hl⟩
      exact (h₂'.not_ge hm).elim
    · exact he
    · have hm := h.next _ ⟨hx ▸ e.1.adj, hx ▸ e.2, hx ▸ hr⟩
      exact (h₁'.not_ge hm).elim
  have hy : e.1.snd = f.1.snd := by
    by_contra hn
    exact D.slope_ne e.1.adj (hx.symm ▸ f.1.adj) e.2 (hx.symm ▸ f.2) hn hs
  exact Subtype.ext (Dart.ext _ _ (Prod.ext hx hy))

private noncomputable def charge [Fintype V] (e : RightEdge D) : V ⊕ (V × Bool) := by
  classical
  exact if h : ∃ c, Above D e c then
    let s := firstStop D (nextGap D h)
    Sum.inr (s.vertex, decide (D.height e.1.fst e.1.snd (D.x s.vertex) < D.y s.vertex))
  else Sum.inl e.1.fst

private theorem charge_injective [Fintype V] : Function.Injective (charge D) := by
  classical
  intro e f hh
  unfold charge at hh
  split at hh <;> split at hh
  · rename_i he hf
    let s := firstStop D (nextGap D he)
    let t := firstStop D (nextGap D hf)
    have hh' : (s.vertex, decide (D.height e.1.fst e.1.snd (D.x s.vertex) < D.y s.vertex)) =
        (t.vertex, decide (D.height f.1.fst f.1.snd (D.x t.vertex) < D.y t.vertex)) :=
      Sum.inr.inj hh
    have hx : s.vertex = t.vertex := congrArg Prod.fst hh'
    have hy : decide (D.height e.1.fst e.1.snd (D.x s.vertex) < D.y s.vertex) =
        decide (D.height f.1.fst f.1.snd (D.x t.vertex) < D.y t.vertex) := congrArg Prod.snd hh'
    rw [← hx, decide_eq_decide] at hy
    obtain ⟨hs, _, _, hs₁, hs₂⟩ := s.stops
    obtain ⟨ht, _, _, ht₁, ht₂⟩ := t.stops
    rw [← hx] at ht ht₁ ht₂
    refine eq_of_overlap D s t hx ?_ ?_
    · by_cases h : D.height e.1.fst e.1.snd (D.x s.vertex) < D.y s.vertex
      · exact h.trans_le ht₂
      · have hw := gap_width D (nextGap D hf) ht
        have hn := not_lt.mpr (le_of_not_gt (fun h' ↦ h (hy.mpr h')))
        linarith
    · by_cases h : D.height f.1.fst f.1.snd (D.x s.vertex) < D.y s.vertex
      · exact h.trans_le hs₂
      · have hw := gap_width D (nextGap D he) hs
        have hn := not_lt.mpr (le_of_not_gt (fun h' ↦ h (hy.mp h')))
        linarith
  · contradiction
  · contradiction
  · rename_i he hf
    have hx := Sum.inl.inj hh
    have hs : D.slope e.1.fst e.1.snd = D.slope e.1.fst f.1.snd := by
      rcases lt_trichotomy (D.slope e.1.fst e.1.snd) (D.slope e.1.fst f.1.snd) with hl | heq | hr
      · exact (he ⟨_, hx.symm ▸ f.1.adj, hx.symm ▸ f.2, hl⟩).elim
      · exact heq
      · exact (hf ⟨_, hx ▸ e.1.adj, hx ▸ e.2, hx ▸ hr⟩).elim
    have hy : e.1.snd = f.1.snd := by
      by_contra hn
      exact D.slope_ne e.1.adj (hx.symm ▸ f.1.adj) e.2 (hx.symm ▸ f.2) hn hs
    exact Subtype.ext (Dart.ext _ _ (Prod.ext hx hy))

private theorem charge_misses_rightmost [Fintype V] [Nonempty V] :
    ∃ v : V, Sum.inl v ∉ Set.range (charge D) := by
  classical
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ D.x Finset.univ_nonempty
  refine ⟨v, ?_⟩
  rintro ⟨e, he⟩
  unfold charge at he
  split at he
  · contradiction
  · have hx := Sum.inl.inj he
    exact e.2.not_ge (hx ▸ hv _ (Finset.mem_univ e.1.snd))

/-- A nonempty finite straight-line planar graph has a vertex of degree at most five. -/
theorem exists_small_degree {V : Type*} [Finite V] [Nonempty V] (G : SimpleGraph V)
    (hG : G.IsPlanar) : ∃ v : V, Nat.card (G.neighborSet v) ≤ 5 := by
  classical
  obtain ⟨D⟩ := drawing_of_planar hG
  let : Fintype V := Fintype.ofFinite V
  let : Fintype (RightEdge D) := Fintype.ofFinite _
  obtain ⟨v, hv⟩ := charge_misses_rightmost D
  have h₁ := Fintype.card_lt_of_injective_of_notMem (charge D) (charge_injective D) hv
  have h₂ := Fintype.card_le_of_injective (orient D) (orient_injective D)
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool] at h₁ h₂
  have h₃ : Fintype.card G.Dart < 6 * Fintype.card V := by omega
  by_contra! h
  have h' (v : V) : 6 ≤ G.degree v := by
    simpa only [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree, Nat.succ_le_iff]
      using h v
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ ↦ h' v)
  rw [← G.dart_card_eq_sum_degrees] at hs
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
  omega

end

/-! ### The signed ray count -/

section

variable {V : Type*} {G : SimpleGraph V} (D : Drawing G)

/-- A horizontal coordinate is in the closed projection of the segment. -/
def Span (a b : V) (x : ℝ) : Prop := min (D.x a) (D.x b) ≤ x ∧ x ≤ max (D.x a) (D.x b)

/-- Swapping the endpoints preserves the closed horizontal span. -/
theorem span_comm (a b : V) (x : ℝ) : Span D a b x ↔ Span D b a x := by
  simp only [Span, min_comm, max_comm]

/-- The closed segment is independent of its orientation. -/
private theorem segment_swap (a b : ℝ × ℝ) : Segment a b = Segment b a := by
  have go (a b : ℝ × ℝ) : Segment a b ⊆ Segment b a := by
    intro p hp
    rcases hp with ⟨t, ht₀, ht₁, hx, hy⟩
    refine ⟨1 - t, sub_nonneg.mpr ht₁, sub_le_self _ ht₀, ?_, ?_⟩
    · rw [hx]
      ring
    · rw [hy]
      ring
  exact Set.Subset.antisymm (go a b) (go b a)

private theorem height_mem {a b : V} {t : ℝ} (h : a ≠ b) (ht : Span D a b t) :
    (t, D.height a b t) ∈ Segment (D.point a) (D.point b) := by
  rcases lt_or_gt_of_ne (D.xinj.ne h) with hl | hr
  · simp only [Span, min_eq_left hl.le, max_eq_right hl.le] at ht
    exact D.height_mem_segment hl ht.1 ht.2
  · simp only [Span, min_eq_right hr.le, max_eq_left hr.le] at ht
    rw [D.height_symm h, segment_swap]
    exact D.height_mem_segment hr ht.1 ht.2

/-- Overlapping vertical projections can have equal height only at a shared graph vertex. -/
theorem shared_of_equal {a b c d : V} {t : ℝ} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hd : ({a, b} : Set V) ≠ {c, d}) (h₁ : Span D a b t) (h₂ : Span D c d t)
    (he : D.height a b t = D.height c d t) :
    ∃ w : V, w ∈ ({a, b} : Set V) ∧ w ∈ ({c, d} : Set V) ∧ D.x w = t := by
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
    D.contact_at_vertex hab hcd hd (height_mem D hab.ne h₁) (he ▸ height_mem D hcd.ne h₂)

/-- Integer indicator. -/
noncomputable def tick (P : Prop) : ℤ := by
  classical
  exact if P then 1 else 0

private theorem tick_sub {x s t : ℝ} (hst : s ≤ t) :
    tick (x ≤ t) - tick (x ≤ s) = tick (s < x ∧ x ≤ t) := by
  by_cases hs : x ≤ s
  · have ht := hs.trans hst
    simp [tick, hs, ht, not_lt_of_ge hs]
  · by_cases ht : x ≤ t <;> simp [tick, hs, ht, lt_of_not_ge hs]

/-- The signed contribution of the oriented edge to the ray from `(t,y)`. -/
noncomputable def rayEdge (a b : V) (t y : ℝ) : ℤ :=
  tick (y < D.height a b t) * (tick (D.x a ≤ t) - tick (D.x b ≤ t))

/-- Reversing an oriented edge negates its ray count. -/
theorem rayEdge_rev {a b : V} (hn : a ≠ b) (t y : ℝ) :
    rayEdge D b a t y = -rayEdge D a b t y := by
  unfold rayEdge
  rw [D.height_symm hn]
  ring

/-- An endpoint contributes if its vertex is above the probe and in `(s,t]`. -/
noncomputable def cut (p q : V) (s t : ℝ) (a : V) : ℤ :=
  tick (s < D.x a ∧ D.x a ≤ t ∧ D.height p q (D.x a) < D.y a)

private theorem edge_diff_forward {a b p q : V} {s t : ℝ} (hab : D.x a < D.x b)
    (hst : s ≤ t) (hsep : ∀ z, s ≤ z → z ≤ t → Span D a b z →
      D.height p q z ≠ D.height a b z) :
    rayEdge D a b t (D.height p q t) - rayEdge D a b s (D.height p q s) =
      cut D p q s t a - cut D p q s t b := by
  let F := ∃ z, s ≤ z ∧ z ≤ t ∧ Span D a b z ∧ D.height p q z < D.height a b z
  have stable (u : ℝ) (hsu : s ≤ u) (hut : u ≤ t) (hu : Span D a b u) :
      (D.height p q u < D.height a b u) ↔ F := by
    refine ⟨fun h ↦ ⟨u, hsu, hut, hu, h⟩, ?_⟩
    rintro ⟨z, hsz, hzt, hz, hl⟩
    rcases le_total z u with hzu | huz
    · apply (D.height_lt_iff hzu ?_).mp hl
      intro w hzw hwu
      exact hsep _ (hsz.trans hzw) (hwu.trans hut) ⟨hz.1.trans hzw, hwu.trans hu.2⟩
    · apply (D.height_lt_iff huz ?_).mpr hl
      intro w huw hwz
      exact hsep _ (hsu.trans huw) (hwz.trans hzt) ⟨hu.1.trans huw, hwz.trans hz.2⟩
  have ray (u : ℝ) (hs : s ≤ u) (ht : u ≤ t) :
      rayEdge D a b u (D.height p q u) =
        tick F * (tick (D.x a ≤ u) - tick (D.x b ≤ u)) := by
    by_cases ha : D.x a ≤ u
    · by_cases hb : D.x b ≤ u
      · simp [rayEdge, tick, ha, hb]
      · have hu : Span D a b u := by
          simpa only [Span, min_eq_left hab.le, max_eq_right hab.le]
            using And.intro ha (lt_of_not_ge hb).le
        rw [rayEdge, stable _ hs ht hu]
    · have hb : ¬ D.x b ≤ u := fun hb ↦ ha (hab.le.trans hb)
      simp [rayEdge, tick, ha, hb]
  have cut_eq (w : V) (hw : Span D a b (D.x w)) (he : D.height a b (D.x w) = D.y w) :
      cut D p q s t w = tick F * (tick (D.x w ≤ t) - tick (D.x w ≤ s)) := by
    rw [cut, tick_sub hst]
    by_cases hs : s < D.x w ∧ D.x w ≤ t
    · rw [← he, stable _ hs.1.le hs.2 hw]
      have hF : (s < D.x w ∧ D.x w ≤ t ∧ F) = F := propext
        ⟨fun h ↦ h.2.2, fun h ↦ ⟨hs.1, hs.2, h⟩⟩
      rw [hF]
      have hOne : tick (s < D.x w ∧ D.x w ≤ t) = 1 := by simp only [tick, ite_eq_left hs]
      rw [hOne, mul_one]
    · have h : ¬(s < D.x w ∧ D.x w ≤ t ∧ D.height p q (D.x w) < D.y w) :=
        fun hc ↦ hs ⟨hc.1, hc.2.1⟩
      simp only [tick, h, hs, ite_false, mul_zero]
  have ha : Span D a b (D.x a) := by
    simpa only [Span, min_eq_left hab.le, max_eq_right hab.le] using And.intro le_rfl hab.le
  have hb : Span D a b (D.x b) := by
    simpa only [Span, min_eq_left hab.le, max_eq_right hab.le] using And.intro hab.le le_rfl
  rw [ray _ hst le_rfl, ray _ le_rfl hst, cut_eq a ha (D.height_left a b),
    cut_eq b hb (D.height_right (ne_of_apply_ne D.x hab.ne))]
  ring

/-- On a noncontacting probe segment the signed ray change telescopes across one edge. -/
theorem edge_diff {a b p q : V} {s t : ℝ} (hn : a ≠ b) (hst : s ≤ t)
    (hsep : ∀ z, s ≤ z → z ≤ t → Span D a b z → D.height p q z ≠ D.height a b z) :
    rayEdge D a b t (D.height p q t) - rayEdge D a b s (D.height p q s) =
      cut D p q s t a - cut D p q s t b := by
  rcases lt_or_gt_of_ne (D.xinj.ne hn) with h | h
  · exact edge_diff_forward D h hst hsep
  · have he := edge_diff_forward D (p := p) (q := q) h hst (by
      intro z hs ht hz
      rw [← D.height_symm hn]
      exact hsep _ hs ht ((span_comm D _ _ _).2 hz))
    rw [rayEdge_rev D hn, rayEdge_rev D hn] at he
    omega

/-- Coordinates for an abstract walk are read from the given drawing. -/
noncomputable def walkRay {W : Type*} {H : SimpleGraph W} (f : W → V)
    {a b : W} (P : H.Walk a b) (t y : ℝ) : ℤ :=
  match P with
  | .nil => 0
  | .cons (u := u) (v := v) _ Q => rayEdge D (f u) (f v) t y + walkRay f Q t y

/-- The change in the signed ray count along a probe telescopes across a walk. -/
theorem walk_diff {W : Type*} {H : SimpleGraph W} (f : W → V) {a b : W}
    (P : H.Walk a b) {p q : V} {s t : ℝ} (hst : s ≤ t)
    (hsep : ∀ ⦃c d : W⦄, H.Adj c d → f c ≠ f d ∧
      ∀ z, s ≤ z → z ≤ t → Span D (f c) (f d) z → D.height p q z ≠ D.height (f c) (f d) z) :
    walkRay D f P t (D.height p q t) - walkRay D f P s (D.height p q s) =
      cut D p q s t (f a) - cut D p q s t (f b) := by
  induction P with
  | nil => simp [walkRay]
  | cons h _ ih =>
    have he := edge_diff D (hsep h).1 hst (hsep h).2
    simp only [walkRay] at he ⊢
    omega

end

/-! ### Alternating spokes -/

section

variable {V : Type*} {G : SimpleGraph V} (D : Drawing G)

private def restricted (P : V → Prop) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ P a ∧ P b
  symm := ⟨fun _ _ h ↦ ⟨Adj.symm (G := G) h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h ↦ G.irrefl h.1⟩

private structure Probe where
  p : V
  q : V
  adj : G.Adj p q
  lo : ℝ
  hi : ℝ
  order : lo ≤ hi
  within : ∀ t, lo ≤ t → t ≤ hi → Span D p q t

private def mkProbe {p q : V} (h : G.Adj p q) (s t : ℝ) (hst : s ≤ t)
    (hs : Span D p q s) (ht : Span D p q t) : Probe D :=
  ⟨p, q, h, s, t, hst, fun _ hl hr ↦ ⟨hs.1.trans hl, hr.trans ht.2⟩⟩

private theorem span_first (a b : V) : Span D a b (D.x a) :=
  ⟨min_le_left .., le_max_left ..⟩

private theorem span_last (a b : V) : Span D a b (D.x b) :=
  ⟨min_le_right .., le_max_right ..⟩

private theorem probe_no_contact (S : Probe D) {a b : V} (hab : G.Adj a b)
    (hne : ({a, b} : Set V) ≠ {S.p, S.q})
    (hn : ∀ w ∈ ({a, b} : Set V), w ∈ ({S.p, S.q} : Set V) →
      ¬(S.lo ≤ D.x w ∧ D.x w ≤ S.hi)) :
    ∀ z, S.lo ≤ z → z ≤ S.hi → Span D a b z → D.height S.p S.q z ≠ D.height a b z := by
  intro z hs ht hz he
  obtain ⟨w, hw, hw', hx⟩ := shared_of_equal D hab S.adj hne hz (S.within z hs ht) he.symm
  exact hn w hw hw' (hx.symm ▸ ⟨hs, ht⟩)

private theorem pair_ne_of_mem_notMem {a b p q w : V} (hw : w ∈ ({a, b} : Set V))
    (hw' : w ≠ p ∧ w ≠ q) : ({a, b} : Set V) ≠ {p, q} := by
  intro he
  rw [he, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  exact hw.elim hw'.1 hw'.2

private theorem path_diff {A : V → Prop} {a c : V} (P : (restricted (G := G) A).Walk a c)
    (S : Probe D) (hp : ¬ A S.p) (hq : ¬ A S.q) :
    walkRay D id P S.hi (D.height S.p S.q S.hi) -
        walkRay D id P S.lo (D.height S.p S.q S.lo) =
      cut D S.p S.q S.lo S.hi a - cut D S.p S.q S.lo S.hi c := by
  apply walk_diff D id P S.order
  intro z w hz
  refine ⟨Adj.ne (G := G) hz.1, probe_no_contact D S hz.1 ?_ ?_⟩
  · exact pair_ne_of_mem_notMem (w := z) (Set.mem_insert z _) ⟨
      fun he ↦ hp (he ▸ hz.2.1), fun he ↦ hq (he ▸ hz.2.1)⟩
  · intro u hu hu'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hu'
    have ha : A u := hu.elim (· ▸ hz.2.1) (· ▸ hz.2.2)
    exact (hu'.elim (fun h ↦ hp (h ▸ ha)) (fun h ↦ hq (h ▸ ha))).elim

private noncomputable def cycleRay {A : V → Prop} {a c : V}
    (v : V) (P : (restricted (G := G) A).Walk a c) (t y : ℝ) : ℤ :=
  rayEdge D v a t y + walkRay D id P t y + rayEdge D c v t y

private theorem cycle_constant {A : V → Prop} {a c v : V}
    (P : (restricted (G := G) A).Walk a c) (hva : G.Adj v a) (hvc : G.Adj v c)
    (ha : A a) (hc : A c) (S : Probe D) (hp : ¬ A S.p) (hq : ¬ A S.q)
    (hv : v ∈ ({S.p, S.q} : Set V) → ¬(S.lo ≤ D.x v ∧ D.x v ≤ S.hi)) :
    cycleRay D v P S.lo (D.height S.p S.q S.lo) =
      cycleRay D v P S.hi (D.height S.p S.q S.hi) := by
  have han : a ≠ S.p ∧ a ≠ S.q := ⟨fun h ↦ hp (h ▸ ha), fun h ↦ hq (h ▸ ha)⟩
  have hcn : c ≠ S.p ∧ c ≠ S.q := ⟨fun h ↦ hp (h ▸ hc), fun h ↦ hq (h ▸ hc)⟩
  have hal := edge_diff D hva.ne S.order
    (probe_no_contact D S hva (pair_ne_of_mem_notMem (Set.mem_insert_of_mem _ rfl) han) (by
      intro w hwa hwp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwa
      rcases hwa with rfl | rfl
      · exact hv hwp
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, han.1, han.2, or_self] at hwp))
  have hcl := edge_diff D hvc.ne' S.order
    (probe_no_contact D S hvc.symm (pair_ne_of_mem_notMem (Set.mem_insert _ _) hcn) (by
      intro w hwc hwp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwc
      rcases hwc with rfl | rfl
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hcn.1, hcn.2, or_self] at hwp
      · exact hv hwp))
  have hpl := path_diff D P S hp hq
  unfold cycleRay
  omega

private theorem near_right [Finite V] {v w : V} (h : D.x v < D.x w) :
    ∃ t, D.x v < t ∧ ∀ z, D.x v < D.x z → t < D.x z := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let s := Finset.univ.filter fun z ↦ D.x v < D.x z
  obtain ⟨z, hz, hzmin⟩ := Finset.exists_min_image s D.x ⟨w, by simp [s, h]⟩
  have hzlt := (Finset.mem_filter.mp hz).2
  refine ⟨(D.x v + D.x z) / 2, by linarith, fun b hb ↦ ?_⟩
  have hzb := hzmin b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
  linarith

private theorem near_left [Finite V] {v w : V} (h : D.x w < D.x v) :
    ∃ t, t < D.x v ∧ ∀ z, D.x z < D.x v → D.x z < t := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let s := Finset.univ.filter fun z ↦ D.x z < D.x v
  obtain ⟨z, hz, hzmax⟩ := Finset.exists_max_image s D.x ⟨w, by simp [s, h]⟩
  have hzlt := (Finset.mem_filter.mp hz).2
  refine ⟨(D.x v + D.x z) / 2, by linarith, fun b hb ↦ ?_⟩
  have hzb := hzmax b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
  linarith

private theorem cut_vanishes {S : Probe D} {a : V} (h : ¬(S.lo < D.x a ∧ D.x a ≤ S.hi)) :
    cut D S.p S.q S.lo S.hi a = 0 := by
  unfold cut
  have hn : ¬(S.lo < D.x a ∧ D.x a ≤ S.hi ∧ D.height S.p S.q (D.x a) < D.y a) :=
    fun he ↦ h ⟨he.1, he.2.1⟩
  simp only [tick, ite_eq_right hn]

private theorem ray_on_right {a v w : V} {t : ℝ} (ht : D.x v ≤ t) (ha : t < D.x a) :
    rayEdge D v a t (D.height v w t) = tick (D.height v w t < D.height v a t) := by
  have h₁ : tick (D.x v ≤ t) = 1 := by simp [tick, ht]
  have h₂ : tick (D.x a ≤ t) = 0 := by simp [tick, ha.not_ge]
  simp only [rayEdge, h₁, h₂, sub_zero, mul_one]

private theorem ray_on_left {a v w : V} {t : ℝ} (hv : t < D.x v) (ha : D.x v < D.x a) :
    rayEdge D v a t (D.height v w t) = 0 := by
  have h₁ : tick (D.x v ≤ t) = 0 := by simp [tick, hv.not_ge]
  have h₂ : tick (D.x a ≤ t) = 0 := by simp [tick, (hv.trans ha).not_ge]
  simp only [rayEdge, h₁, h₂, sub_self, mul_zero]

private theorem path_near_center {A : V → Prop} {a c v w : V}
    (P : (restricted (G := G) A).Walk a c) (ha : A a) (hc : A c)
    (hv : ¬ A v) (hw : ¬ A w) (hvw : G.Adj v w)
    {t : ℝ} (ht : Span D v w t)
    (hbetween : ∀ z, A z → ¬(min (D.x v) t ≤ D.x z ∧ D.x z ≤ max (D.x v) t)) :
    walkRay D id P t (D.height v w t) = walkRay D id P (D.x v) (D.y v) := by
  let S := mkProbe D hvw (min (D.x v) t) (max (D.x v) t) (min_le_max ..)
    (by rcases le_total (D.x v) t with h | h
        · simpa only [min_eq_left h] using span_first D v w
        · simpa only [min_eq_right h] using ht)
    (by rcases le_total (D.x v) t with h | h
        · simpa only [max_eq_right h] using ht
        · simpa only [max_eq_left h] using span_first D v w)
  have hzero {z : V} (hz : A z) : cut D S.p S.q S.lo S.hi z = 0 :=
    cut_vanishes D (fun h ↦ hbetween z hz ⟨h.1.le, h.2⟩)
  have hd := path_diff D P S hv hw
  rw [hzero ha, hzero hc, sub_self, sub_eq_zero] at hd
  change walkRay D id P (max (D.x v) t) (D.height v w (max (D.x v) t)) =
    walkRay D id P (min (D.x v) t) (D.height v w (min (D.x v) t)) at hd
  rcases le_total (D.x v) t with h | h
  · simpa only [max_eq_right h, min_eq_left h, D.height_left] using hd
  · simpa only [max_eq_left h, min_eq_right h, D.height_left] using hd.symm

private theorem cycle_at_right {A : V → Prop} {a c v w : V} [Finite V]
    (P : (restricted (G := G) A).Walk a c) (ha : A a) (hc : A c)
    (hv : ¬ A v) (hw : ¬ A w) (hva : G.Adj v a) (hvc : G.Adj v c) (hvw : G.Adj v w)
    (hxa : D.x v < D.x a) (hxc : D.x v < D.x c) (hxw : D.x v < D.x w) :
    cycleRay D v P (D.x w) (D.y w) =
      tick (D.slope v w < D.slope v a) + walkRay D id P (D.x v) (D.y v) -
        tick (D.slope v w < D.slope v c) := by
  obtain ⟨t, hvt, hnear⟩ := near_right D hxw
  have htw := hnear w hxw
  have hspan : Span D v w t := by
    exact ⟨(min_le_left ..).trans hvt.le, htw.le.trans (le_max_right ..)⟩
  let S := mkProbe D hvw t (D.x w) htw.le hspan (span_last D v w)
  have he := cycle_constant D P hva hvc ha hc S hv hw (fun _ h ↦ hvt.not_ge h.1)
  have hP := path_near_center D P ha hc hv hw hvw hspan (by
    intro z hz
    have hne : z ≠ v := fun h ↦ hv (h ▸ hz)
    rw [min_eq_left hvt.le, max_eq_right hvt.le]
    exact fun h ↦ (hnear z (lt_of_le_of_ne h.1 (D.xinj.ne hne.symm))).not_ge h.2)
  change cycleRay D v P t (D.height v w t) =
    cycleRay D v P (D.x w) (D.height v w (D.x w)) at he
  rw [D.height_right hvw.ne] at he
  rw [← he, cycleRay, rayEdge_rev D hvc.ne, ray_on_right D hvt.le (hnear a hxa),
    ray_on_right D hvt.le (hnear c hxc), hP, D.height_lt_iff_slope hvt,
    D.height_lt_iff_slope hvt, sub_eq_add_neg]

private theorem cycle_at_left {A : V → Prop} {a c v w : V} [Finite V]
    (P : (restricted (G := G) A).Walk a c) (ha : A a) (hc : A c)
    (hv : ¬ A v) (hw : ¬ A w) (hva : G.Adj v a) (hvc : G.Adj v c) (hvw : G.Adj v w)
    (hxa : D.x v < D.x a) (hxc : D.x v < D.x c) (hxw : D.x w < D.x v) :
    cycleRay D v P (D.x w) (D.y w) = walkRay D id P (D.x v) (D.y v) := by
  obtain ⟨t, htv, hnear⟩ := near_left D hxw
  have hwt := hnear w hxw
  have hspan : Span D v w t := by
    exact ⟨(min_le_right ..).trans hwt.le, htv.le.trans (le_max_left ..)⟩
  let S := mkProbe D hvw (D.x w) t hwt.le (span_last D v w) hspan
  have he := cycle_constant D P hva hvc ha hc S hv hw (fun _ h ↦ htv.not_ge h.2)
  have hP := path_near_center D P ha hc hv hw hvw hspan (by
    intro z hz
    have hne : z ≠ v := fun h ↦ hv (h ▸ hz)
    rw [min_eq_right htv.le, max_eq_left htv.le]
    exact fun h ↦ (hnear z (lt_of_le_of_ne h.2 (D.xinj.ne hne))).not_ge h.1)
  change cycleRay D v P (D.x w) (D.height v w (D.x w)) =
    cycleRay D v P t (D.height v w t) at he
  rw [D.height_right hvw.ne] at he
  rw [he, cycleRay, rayEdge_rev D hvc.ne, ray_on_left D htv hxa, ray_on_left D htv hxc, hP]
  simp

private theorem cycle_eq_at_adj {A : V → Prop} {a c v p q : V}
    (P : (restricted (G := G) A).Walk a c) (ha : A a) (hc : A c)
    (hva : G.Adj v a) (hvc : G.Adj v c) (hpq : G.Adj p q) (hp : ¬ A p) (hq : ¬ A q)
    (hpv : p ≠ v) (hqv : q ≠ v) :
    cycleRay D v P (D.x p) (D.y p) = cycleRay D v P (D.x q) (D.y q) := by
  have make (s t : ℝ) (hst : s ≤ t) (hs : Span D p q s) (ht : Span D p q t) :=
    cycle_constant D P hva hvc ha hc (mkProbe D hpq s t hst hs ht) hp hq (by
      intro hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      exact (hw.elim (fun h ↦ hpv h.symm) (fun h ↦ hqv h.symm)).elim)
  rcases le_total (D.x p) (D.x q) with h | h
  · simpa only [mkProbe, D.height_left, D.height_right hpq.ne] using
      make _ _ h (span_first D p q) (span_last D p q)
  · simpa only [mkProbe, D.height_left, D.height_right hpq.ne] using
      (make _ _ h (span_last D p q) (span_first D p q)).symm

private theorem alternating_paths_impossible [Finite V] {A B : V → Prop} {v a b c d : V}
    (P : (restricted (G := G) A).Walk a c) (Q : (restricted (G := G) B).Walk b d)
    (ha : A a) (hc : A c) (hb : B b) (hd : B d)
    (hvA : ¬ A v) (hvB : ¬ B v) (hAB : ∀ ⦃w⦄, B w → ¬ A w)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c) (hvd : G.Adj v d)
    (hxa : D.x v < D.x a) (hxb : D.x v < D.x b) (hxc : D.x v < D.x c)
    (hsab : D.slope v a < D.slope v b) (hsbc : D.slope v b < D.slope v c)
    (hxd : D.x d < D.x v ∨ D.x v < D.x d ∧ D.slope v c < D.slope v d) : False := by
  have along : ∀ {s t : V}, (restricted (G := G) B).Walk s t →
      cycleRay D v P (D.x s) (D.y s) = cycleRay D v P (D.x t) (D.y t) := by
    intro s t R
    induction R with
    | nil => rfl
    | cons h _ ih =>
      exact (cycle_eq_at_adj D P ha hc hva hvc h.1 (hAB h.2.1) (hAB h.2.2)
        (fun he ↦ hvB (he ▸ h.2.1)) (fun he ↦ hvB (he ▸ h.2.2))).trans ih
  have hQ := along Q
  have ht : tick (D.slope v b < D.slope v a) = 0 := by simp [tick, hsab.not_gt]
  have hu : tick (D.slope v b < D.slope v c) = 1 := by simp [tick, hsbc]
  rw [cycle_at_right D P ha hc hvA (hAB hb) hva hvc hvb hxa hxc hxb, ht, hu] at hQ
  rcases hxd with hl | ⟨hr, hs⟩
  · rw [cycle_at_left D P ha hc hvA (hAB hd) hva hvc hvd hxa hxc hl] at hQ
    omega
  · have hda : ¬ D.slope v d < D.slope v a := ((hsab.trans hsbc).trans hs).not_gt
    rw [cycle_at_right D P ha hc hvA (hAB hd) hva hvc hvd hxa hxc hr] at hQ
    have h₁ : tick (D.slope v d < D.slope v a) = 0 := by simp [tick, hda]
    have h₂ : tick (D.slope v d < D.slope v c) = 0 := by simp [tick, hs.not_gt]
    rw [h₁, h₂] at hQ
    omega

private def flip (p : ℝ × ℝ) : ℝ × ℝ := (-p.1, p.2)

private theorem flip_flip (p : ℝ × ℝ) : flip (flip p) = p := by
  exact Prod.ext (neg_neg _) rfl

private theorem flip_segment {a b p : ℝ × ℝ} :
    flip p ∈ Segment (flip a) (flip b) ↔ p ∈ Segment a b := by
  constructor <;> rintro ⟨t, ht₀, ht₁, hx, hy⟩ <;> refine ⟨t, ht₀, ht₁, ?_, hy⟩
  all_goals dsimp only [flip] at hx ⊢; linear_combination -hx

private def flipped : Drawing G where
  point := flip ∘ D.point
  xinj := fun a b h ↦ D.xinj (neg_injective h)
  meet := by
    intro a b c d hab hcd hd p hp
    obtain ⟨q, rfl⟩ := (show Function.Surjective flip from fun p ↦ ⟨flip p, flip_flip p⟩) p
    have hf : Function.Injective flip := fun _ _ he ↦
      (flip_flip _).symm.trans ((congrArg flip he).trans (flip_flip _))
    have hm := D.meet hab hcd hd ⟨flip_segment.mp hp.1, flip_segment.mp hp.2⟩
    simpa only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Function.comp_apply, hf.eq_iff] using hm

private noncomputable def rightNeighbors (v : V) [Fintype (G.neighborSet v)] :
    Finset (G.neighborSet v) := by
  classical
  exact Finset.univ.filter fun w ↦ D.x v < D.x w.val

private theorem many_right_or_reflect (D : Drawing G) {v : V} [Fintype (G.neighborSet v)]
    (hcard : Fintype.card (G.neighborSet v) = 5) :
    ∃ E : Drawing G, 3 ≤ (rightNeighbors E v).card := by
  classical
  by_cases hd : 3 ≤ (rightNeighbors D v).card
  · exact ⟨D, hd⟩
  · have hflip : rightNeighbors (flipped D) v =
        Finset.univ.filter fun w : G.neighborSet v ↦ ¬ D.x v < D.x w.val := by
      ext w
      have hne := D.xinj.ne (Adj.ne (G := G) w.prop)
      simp only [rightNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
      change -D.x v < -D.x w.val ↔ ¬ D.x v < D.x w.val
      rw [neg_lt_neg_iff, not_lt]
      exact lt_iff_le_and_ne.trans (and_iff_left hne.symm)
    have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun w : G.neighborSet v ↦ D.x v < D.x w.val)
    change (rightNeighbors D v).card +
      (Finset.univ.filter fun w : G.neighborSet v ↦ ¬ D.x v < D.x w.val).card = _ at hsplit
    rw [← hflip, Finset.card_univ, hcard] at hsplit
    exact ⟨flipped D, by omega⟩

private theorem right_sorted {v : V} [Fintype (G.neighborSet v)] {k : ℕ}
    (hk : k ≤ (rightNeighbors D v).card) :
    ∃ e : Fin k → G.neighborSet v,
      (∀ i, D.x v < D.x (e i).val) ∧ StrictMono (fun i ↦ D.slope v (e i).val) := by
  classical
  let R := rightNeighbors D v
  let slope := fun w : G.neighborSet v ↦ D.slope v w.val
  have right_of_mem {w : G.neighborSet v} (hw : w ∈ R) : D.x v < D.x w.val :=
    (Finset.mem_filter.mp hw).2
  have hinj : Set.InjOn slope ↑R := by
    intro p hp q hq he
    by_contra hn
    exact D.slope_ne p.prop q.prop (right_of_mem hp) (right_of_mem hq)
      (fun he' ↦ hn (Subtype.ext he')) he
  have hcard : k ≤ (R.image slope).card := by
    rw [Finset.card_image_of_injOn hinj]
    exact hk
  let order := (R.image slope).orderEmbOfCardLe hcard
  have choose (i : Fin k) : ∃ w ∈ R, slope w = order i :=
    Finset.mem_image.mp (Finset.orderEmbOfCardLe_mem _ _ _)
  refine ⟨fun i ↦ (choose i).choose, fun i ↦ right_of_mem (choose i).choose_spec.1, ?_⟩
  intro i j hij
  change slope (choose i).choose < slope (choose j).choose
  rw [(choose i).choose_spec.2, (choose j).choose_spec.2]
  exact order.strictMono hij

private theorem pick_spokes {v : V} [Fintype (G.neighborSet v)]
    (hc : Fintype.card (G.neighborSet v) = 5) (hR : 3 ≤ (rightNeighbors D v).card) :
    ∃ a b c d : G.neighborSet v, D.x v < D.x a.val ∧ D.x v < D.x b.val ∧ D.x v < D.x c.val ∧
      D.slope v a.val < D.slope v b.val ∧ D.slope v b.val < D.slope v c.val ∧
      (D.x d.val < D.x v ∨ D.x v < D.x d.val ∧ D.slope v c.val < D.slope v d.val) := by
  classical
  by_cases h : 4 ≤ (rightNeighbors D v).card
  · obtain ⟨e, he, hmono⟩ := right_sorted D h
    exact ⟨e 0, e 1, e 2, e 3, he 0, he 1, he 2,
      hmono (by decide), hmono (by decide), Or.inr ⟨he 3, hmono (by decide)⟩⟩
  · obtain ⟨e, he, hmono⟩ := right_sorted D hR
    have hex : ∃ d : G.neighborSet v, d ∉ rightNeighbors D v := by
      by_contra! hn
      have hall : rightNeighbors D v = Finset.univ := Finset.eq_univ_of_forall hn
      rw [hall, Finset.card_univ, hc] at h
      omega
    obtain ⟨d, hd⟩ := hex
    have hxd : D.x d.val < D.x v := by
      have hn : ¬ D.x v < D.x d.val := fun hh ↦ hd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
      exact lt_of_le_of_ne (le_of_not_gt hn) (D.xinj.ne (Adj.ne' (G := G) d.prop))
    exact ⟨e 0, e 1, e 2, d, he 0, he 1, he 2,
      hmono (by decide), hmono (by decide), Or.inl hxd⟩

private def colorPair {v : V} (C : (deleted G v).Coloring (Fin 5)) (i j : Fin 5) (z : V) : Prop :=
  ∃ w : Away v, w.val = z ∧ (C w = i ∨ C w = j)

private def colorLift {v : V} (C : (deleted G v).Coloring (Fin 5)) (i j : Fin 5) :
    kempe C i j →g restricted (G := G) (colorPair C i j) :=
  ⟨Subtype.val, fun {x y} h ↦ ⟨h.1, ⟨x, rfl, h.2.1⟩, ⟨y, rfl, h.2.2⟩⟩⟩

private theorem not_center_color {v : V} (C : (deleted G v).Coloring (Fin 5)) (i j : Fin 5) :
    ¬ colorPair C i j v := fun ⟨w, h, _⟩ ↦ w.prop h

/-- In the all-five-colors case, not both pairs of alternating spokes can be joined by
bichromatic paths. -/
theorem local_kempe_of_planar {V : Type*} [Finite V] (G : SimpleGraph V) (hG : G.IsPlanar)
    (v : V) : LocalKempe G v := by
  classical
  intro C hb
  let : Nonempty V := ⟨v⟩
  let : Fintype (G.neighborSet v) := Fintype.ofFinite _
  let col : G.neighborSet v → Fin 5 := fun w ↦ C (restrictNeighbor w)
  have hc : Fintype.card (G.neighborSet v) = 5 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (Equiv.ofBijective col hb)
  obtain ⟨D₀⟩ := drawing_of_planar hG
  obtain ⟨D, hR⟩ := many_right_or_reflect D₀ hc
  obtain ⟨a, b, c, d, hxa, hxb, hxc, hab, hbc, hxd⟩ := pick_spokes D hc hR
  have ha_b : a ≠ b := ne_of_apply_ne (fun w : G.neighborSet v ↦ D.slope v w.val) hab.ne
  have hb_c : b ≠ c := ne_of_apply_ne (fun w : G.neighborSet v ↦ D.slope v w.val) hbc.ne
  have ha_c : a ≠ c := ne_of_apply_ne (fun w : G.neighborSet v ↦ D.slope v w.val) (hab.trans hbc).ne
  have ne_d (w : G.neighborSet v) (hxw : D.x v < D.x w.val)
      (hsw : D.slope v w.val ≤ D.slope v c.val) : w ≠ d := by
    intro hn
    rw [hn] at hxw hsw
    exact hxd.elim (lt_asymm hxw) (fun h ↦ h.2.not_ge hsw)
  have ha_d := ne_d a hxa (hab.trans hbc).le
  have hb_d := ne_d b hxb hbc.le
  have hc_d := ne_d c hxc le_rfl
  by_cases hp : (kempe C (col a) (col c)).Reachable (restrictNeighbor a) (restrictNeighbor c)
  · refine ⟨b, d, hb_d, fun hq ↦ ?_⟩
    obtain ⟨P⟩ := hp.map (colorLift C (col a) (col c))
    obtain ⟨Q⟩ := hq.map (colorLift C (col b) (col d))
    have hdis : ∀ ⦃w⦄, colorPair C (col b) (col d) w → ¬ colorPair C (col a) (col c) w := by
      rintro w ⟨u, rfl, hu⟩ ⟨z, hz, hzC⟩
      have he : z = u := Subtype.ext hz
      subst z
      rcases hu with hu | hu <;> rcases hzC with hzC | hzC
      · exact ha_b (hb.injective (hzC.symm.trans hu))
      · exact hb_c (hb.injective (hu.symm.trans hzC))
      · exact ha_d (hb.injective (hzC.symm.trans hu))
      · exact hc_d (hb.injective (hzC.symm.trans hu))
    exact alternating_paths_impossible D P Q
      ⟨restrictNeighbor a, rfl, Or.inl rfl⟩ ⟨restrictNeighbor c, rfl, Or.inr rfl⟩
      ⟨restrictNeighbor b, rfl, Or.inl rfl⟩ ⟨restrictNeighbor d, rfl, Or.inr rfl⟩
      (not_center_color C _ _) (not_center_color C _ _) hdis
      a.prop b.prop c.prop d.prop hxa hxb hxc hab hbc hxd
  · exact ⟨a, c, ha_c, hp⟩

end

end FiveColor

@[expose] public section

/-- **Five color theorem.** Every straight-line planar simple graph $G$ on a finite vertex set
has a proper vertex coloring with five colors.

Source: https://en.wikipedia.org/wiki/Five_color_theorem (statement five-color-s1). -/
theorem five_color_theorem {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : G.IsPlanar) :
    Nonempty (G.Coloring (Fin 5)) := by
  suffices ∀ n (W : Type _) [Finite W], Nat.card W = n →
      ∀ H : SimpleGraph W, H.IsPlanar → Nonempty (H.Coloring (Fin 5)) by
    exact this (Nat.card V) V rfl G hG
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro W _ hn H hH
    cases isEmpty_or_nonempty W with
    | inl he => exact ⟨Coloring.ofIsEmpty⟩
    | inr he =>
      obtain ⟨v, hv⟩ := FiveColor.exists_small_degree H hH
      let : Fintype W := Fintype.ofFinite W
      let : Fintype (FiveColor.Away v) := Fintype.ofFinite (FiveColor.Away v)
      have hlt : Nat.card (FiveColor.Away v) < n := by
        rw [← hn, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact Fintype.card_lt_of_injective_of_notMem Subtype.val Subtype.val_injective
          (b := v) (fun ⟨w, hw⟩ ↦ w.prop hw)
      obtain ⟨C⟩ := ih _ hlt (FiveColor.Away v) rfl (FiveColor.deleted H v)
        (FiveColor.planar_deleted hH v)
      exact FiveColor.extend_five C hv (FiveColor.local_kempe_of_planar H hH v)

end

end MetaMathlibExt
