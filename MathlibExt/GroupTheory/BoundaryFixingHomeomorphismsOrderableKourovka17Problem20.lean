/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Topology.UnitInterval
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Orderability of boundary-fixing homeomorphisms of the disc (Kourovka Notebook Problem 17.20)

Kourovka Notebook, Archive of Solved Problems, Problem 17.20 (G. M. Bergman): if `M` is a real
manifold with nonempty boundary, and `G` the group of self-homeomorphisms of `M` which fix the
boundary pointwise, is `G` right-orderable?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.20 (G. M.
Bergman). UnsolvedMath record UM-00701322 (`KOU-17.20`), dataset ulamai/UnsolvedMath v1.8.0.

The resolution is a counterexample on the closed disc, modelled as the square `I² = [0, 1]²` with
its boundary, as in the source; the target is that this group, `fixingSubgroup` of the boundary in
`I² ≃ₜ I²`, has a right order (a linear order invariant under right multiplication). Its refutation
answers the general question negatively. Left- and right-orderability are equivalent (`g ↦ g⁻¹`).

We prove `discBoundaryFixingHomeomorphismsRightOrderable_refuted` by a variant of Hyde's
periodic shear construction. Write `a` and `b` for the horizontal and vertical unit translations.
We express `b ^ 9` and `b⁻¹ ^ 9` as products of eight factors that commute with `b` and square
to `a` or `a⁻¹`. In a left order this forces `max b b⁻¹ < max a a⁻¹`. Interchanging the
coordinates gives the opposite inequality.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.BoundaryFixingHomeomorphismsOrderableKourovka17Problem20Wanted

/-- **The closed square.** The closed square $I^2 = [0, 1] \times [0, 1]$, the product of two
copies of the unit interval, used as a model of the closed disc. -/
abbrev Square : Type := unitInterval × unitInterval

/-- **Boundary of the square.** The boundary $\partial I^2$ of the closed square
$I^2 = [0, 1] \times [0, 1]$ is the set of points $(x, y) \in I^2$ with $x = 0$, $x = 1$, $y = 0$
or $y = 1$. -/
def squareBoundary : Set Square := {x | x.1 = 0 ∨ x.1 = 1 ∨ x.2 = 0 ∨ x.2 = 1}

/-- **Boundary-fixing homeomorphisms of the square.** Let $I^2 = [0, 1] \times [0, 1]$ be the
closed square and $\partial I^2$ its boundary. $\mathrm{Homeo}(I^2; \partial I^2)$ is the subgroup
of the group of homeomorphisms of $I^2$ consisting of those homeomorphisms $h$ with $h(x) = x$ for
every $x \in \partial I^2$. -/
def boundaryFixingHomeomorphisms : Subgroup (Square ≃ₜ Square) :=
  fixingSubgroup (Square ≃ₜ Square) squareBoundary

/-- The right orders of `G`: linear orders (as relations) invariant under right multiplication. -/
def rightOrders (G : Type*) [Group G] : Set (G → G → Prop) :=
  {r | IsLinearOrder G r ∧ ∀ a b c : G, r a b → r (a * c) (b * c)}

/-- **Right-orderability of the boundary-fixing homeomorphisms of the disc.** The proposition
(Kourovka Problem 17.20, G. M. Bergman, for the closed disc) that the group
$\mathrm{Homeo}(I^2; \partial I^2)$ of homeomorphisms of the closed square
$I^2 = [0, 1] \times [0, 1]$, a model of the closed disc, that fix the boundary $\partial I^2$
pointwise is right-orderable: it carries a linear order $\le$ such that $a \le b$ implies
$ac \le bc$ for all $a, b, c$. -/
def discBoundaryFixingHomeomorphismsRightOrderable : Prop :=
  (rightOrders boundaryFixingHomeomorphisms).Nonempty

noncomputable section

open Filter Topology

/-! ### Bounds on products in a left-ordered group -/

/-- A short factorization of `b ^ 9` by elements commuting with `b` whose squares are
`a` or `a⁻¹`. In a left order it forces `max b b⁻¹ < max a a⁻¹` when it holds for both
`b` and `b⁻¹` and `b ≠ 1`. -/
private def factors {G : Type*} [Group G] (a b : G) : Prop :=
  ∃ l : List G, l.length < 9 ∧ l.prod = b ^ 9 ∧
    ∀ g ∈ l, (g ^ 2 = a ∨ g ^ 2 = a⁻¹) ∧ Commute g b

private lemma factors_map {G H : Type*} [Group G] [Group H] (j : G →* H) {a b : G}
    (h : factors a b) : factors (j a) (j b) := by
  obtain ⟨l, hl, hp, hg⟩ := h
  refine ⟨l.map j, by simpa using hl, ?_, ?_⟩
  · rw [← map_list_prod, hp, map_pow]
  · intro z hz
    obtain ⟨g, hg', rfl⟩ := List.mem_map.mp hz
    obtain ⟨he, hc⟩ := hg g hg'
    exact ⟨by simpa only [← map_pow, ← map_inv] using he.imp (congrArg j) (congrArg j), hc.map j⟩

private lemma product_bound {G : Type*} [Group G] [LinearOrder G] [MulLeftMono G] (t : G)
    (l : List G) (h : ∀ g ∈ l, g ≤ t ∧ Commute g t) : l.prod ≤ t ^ l.length := by
  induction l with
  | nil => simp
  | cons g l ih =>
    obtain ⟨hgt, hc⟩ := h g (by simp)
    calc
      (g :: l).prod ≤ g * t ^ l.length :=
        mul_le_mul_right (ih (fun k hk ↦ h k (List.mem_cons_of_mem _ hk))) _
      _ = t ^ l.length * g := (hc.pow_right _).eq
      _ ≤ t ^ (g :: l).length := by
        simpa only [List.length_cons, pow_succ] using mul_le_mul_right hgt (t ^ l.length)

private lemma violates_bound {G : Type*} [Group G] [LinearOrder G] [MulLeftMono G]
    {a b : G} (h : factors a b) (ha : a ≤ b) (ha' : a⁻¹ ≤ b) (hb : 1 < b) : False := by
  obtain ⟨l, hl, he, hg⟩ := h
  have hh := product_bound b l (by
    intro g hgl
    obtain ⟨hsq, hc⟩ := hg g hgl
    refine ⟨?_, hc⟩
    by_contra! h'
    have h₂ : g < g ^ 2 := by
      simpa only [sq, mul_one] using mul_lt_mul_right (hb.trans h') g
    rcases hsq with hsq | hsq
    · exact (not_lt_of_ge ha) (hsq ▸ h'.trans h₂)
    · exact (not_lt_of_ge ha') (hsq ▸ h'.trans h₂))
  exact (not_le_of_gt (pow_lt_pow_right' hb hl)) (he ▸ hh)

private lemma dominates {G : Type*} [Group G] [LinearOrder G] [MulLeftMono G] {a b : G}
    (hb : b ≠ 1) (hf : factors a b) (hi : factors a b⁻¹) :
    max b b⁻¹ < max a a⁻¹ := by
  by_contra! h
  rcases lt_or_gt_of_ne hb with hb | hb
  · have h₁ : 1 < b⁻¹ := by simpa using mul_lt_mul_right hb b⁻¹
    rw [max_eq_right (hb.trans h₁).le, max_le_iff] at h
    exact violates_bound hi h.1 h.2 h₁
  · have h₁ : b⁻¹ < 1 := by simpa using mul_lt_mul_right hb b⁻¹
    rw [max_eq_left (h₁.trans hb).le, max_le_iff] at h
    exact violates_bound hf h.1 h.2 hb

private lemma exclude_order {G : Type*} [Group G] {a b : G} (ha : a ≠ 1) (hb : b ≠ 1)
    (hab : factors a b) (habi : factors a b⁻¹) (hba : factors b a) (hbai : factors b a⁻¹) :
    ¬ ∃ s : G → G → Prop, IsLinearOrder G s ∧ ∀ a b c : G, s a b → s (c * a) (c * b) := by
  classical
  rintro ⟨s, hs, hm⟩
  let _ : LE G := ⟨s⟩
  let _ : LinearOrder G :=
    { le := s
      le_refl := hs.refl
      le_trans := hs.trans
      le_antisymm := hs.antisymm
      le_total := hs.total
      toDecidableLE := Classical.decRel _ }
  let _ : MulLeftMono G := ⟨fun c _ _ h ↦ hm _ _ c h⟩
  exact lt_asymm (dominates hb hab habi) (dominates ha hba hbai)

/-- Invert and pull back a right order to obtain a left order on an embedded group. -/
private theorem reduceToSubgroup {H : Type*} [Group H] (j : H →* boundaryFixingHomeomorphisms)
    (hj : Function.Injective j)
    (h : ¬ ∃ s : H → H → Prop, IsLinearOrder H s ∧
      ∀ a b c : H, s a b → s (c * a) (c * b)) :
    ¬ discBoundaryFixingHomeomorphismsRightOrderable := by
  rintro ⟨r, hr, hinv⟩
  let : IsLinearOrder _ r := hr
  let f (x : H) := j x⁻¹
  apply h
  refine ⟨InvImage r f, InvImage.isLinearOrder (hj.comp inv_injective), ?_⟩
  intro a b c hab
  change r (j (c * a)⁻¹) (j (c * b)⁻¹)
  simpa only [mul_inv_rev, map_mul] using hinv (f a) (f b) (j c⁻¹) hab

/-! ### Extending bounded-displacement homeomorphisms to the square -/

private abbrev Plane := ℝ × ℝ

private abbrev Disc := {p : Plane // ‖p‖ ≤ 1}

private def height (p : Disc) := 1 - ‖p.val‖
/-- Radial compactification in the sup norm identifies the plane with the square's interior. -/
private def chart (v : Plane) : Disc :=
  ⟨(1 + ‖v‖)⁻¹ • v, by
    have h : 0 < 1 + ‖v‖ := by positivity
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h, inv_mul_eq_div,
      div_le_one h]
    linarith⟩

private lemma height_chart (v : Plane) : height (chart v) = (1 + ‖v‖)⁻¹ := by
  have h : 0 < 1 + ‖v‖ := by positivity
  simp only [height, chart, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h]
  field_simp
  ring

private def decode (p : Disc) : Plane := (height p)⁻¹ • p.val

private lemma decode_chart (v : Plane) : decode (chart v) = v := by
  have h : 0 < 1 + ‖v‖ := by positivity
  rw [decode, height_chart]
  simp [chart, smul_smul, h.ne']

private lemma chart_decode {p : Disc} (hp : height p ≠ 0) : chart (decode p) = p := by
  have ht : 0 < height p := lt_of_le_of_ne (sub_nonneg.mpr p.property) (Ne.symm hp)
  have he : 1 + ‖decode p‖ = (height p)⁻¹ := by
    rw [decode, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    field_simp
    simp [height]
  apply Subtype.ext
  change (1 + ‖decode p‖)⁻¹ • (height p)⁻¹ • p.val = p.val
  simp [he, smul_smul, hp]

private def extend (f : Plane → Plane) (p : Disc) : Disc :=
  if height p = 0 then p else chart (f (decode p))

private lemma extend_chart (f : Plane → Plane) (v : Plane) :
    extend f (chart v) = chart (f v) := by
  have h : 0 < 1 + ‖v‖ := by positivity
  simp [extend, height_chart, h.ne', decode_chart]

/-- In the homogeneous coordinates `(p, height p)`, a bounded displacement is multiplied
by the height and hence tends to zero at the boundary. Renormalizing gives the extension. -/
private lemma continuous_extend {f : Plane → Plane} (hf : Continuous f)
    (hb : ∃ C, ∀ v, ‖f v - v‖ ≤ C) : Continuous (extend f) := by
  obtain ⟨C, hC⟩ := hb
  let q (p : Disc) := p.val + height p • (f (decode p) - decode p)
  have ht : Continuous height := continuous_const.sub continuous_subtype_val.norm
  have hq : Continuous q := by
    apply Continuous.add continuous_subtype_val
    refine continuous_iff_continuousAt.mpr fun p ↦ ?_
    by_cases hp : height p = 0
    · have h₀ : Tendsto height (𝓝 p) (𝓝 0) := hp ▸ ht.continuousAt
      simpa only [ContinuousAt, hp, zero_smul] using
        h₀.zero_smul_isBoundedUnder_le (g := fun s ↦ f (decode s) - decode s)
          (isBoundedUnder_of_eventually_le (a := C) (Eventually.of_forall fun s ↦ hC (decode s)))
    · have hd : ContinuousAt decode p :=
        (ht.continuousAt.inv₀ hp).smul continuous_subtype_val.continuousAt
      exact ht.continuousAt.smul ((hf.continuousAt.comp hd).sub hd)
  have denom (p : Disc) : height p + ‖q p‖ ≠ 0 := by
    by_cases hp : height p = 0
    · have hn : ‖p.val‖ = 1 := (sub_eq_zero.mp hp).symm
      simp [q, hp, hn]
    · have htpos : 0 < height p := lt_of_le_of_ne (sub_nonneg.mpr p.property) (Ne.symm hp)
      positivity
  apply Continuous.subtype_mk
  refine (((ht.add hq.norm).inv₀ denom).smul hq).congr fun p ↦ ?_
  change (height p + ‖q p‖)⁻¹ • q p = (extend f p).val
  by_cases hp : height p = 0
  · have hn : ‖p.val‖ = 1 := (sub_eq_zero.mp hp).symm
    simp [q, extend, hp, hn]
  · have htpos : 0 < height p := lt_of_le_of_ne (sub_nonneg.mpr p.property) (Ne.symm hp)
    have hq' : q p = height p • f (decode p) := by
      dsimp only [q]
      rw [smul_sub]
      simp [decode, smul_smul, hp]
    simp only [extend, hp, ite_false, hq', chart, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos, smul_smul]
    congr 1
    field_simp

/-- The subgroup of plane homeomorphisms with uniformly bounded displacement. -/
private def boundedPlane : Subgroup (Plane ≃ₜ Plane) where
  carrier := {f | ∃ C, ∀ v, ‖f v - v‖ ≤ C}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro f g ⟨C, hC⟩ ⟨D, hD⟩
    refine ⟨C + D, fun v ↦ ?_⟩
    exact (norm_sub_le_norm_sub_add_norm_sub _ (g v) _).trans (add_le_add (hC _) (hD _))
  inv_mem' := by
    rintro f ⟨C, hC⟩
    refine ⟨C, fun v ↦ ?_⟩
    simpa [norm_sub_rev (f.symm v) v] using hC (f.symm v)

private lemma disc_cases (p : Disc) : height p = 0 ∨ ∃ v, p = chart v := by
  by_cases hp : height p = 0
  · exact Or.inl hp
  · exact Or.inr ⟨_, (chart_decode hp).symm⟩

private def discAction (f : boundedPlane) : Disc ≃ₜ Disc where
  toFun := extend f.val
  invFun := extend f.val.symm
  left_inv p := by
    obtain h | ⟨v, rfl⟩ := disc_cases p
    · simp [extend, h]
    · simp [extend_chart]
  right_inv p := by
    obtain h | ⟨v, rfl⟩ := disc_cases p
    · simp [extend, h]
    · simp [extend_chart]
  continuous_toFun := continuous_extend f.val.continuous f.property
  continuous_invFun := continuous_extend f.val.symm.continuous (boundedPlane.inv_mem f.property)

private def scaledCoord (x : ℝ) (h : |x| ≤ 1) : unitInterval :=
  ⟨(x + 1) / 2, by obtain ⟨hl, hu⟩ := abs_le.mp h; constructor <;> linarith⟩

private def squareChart : Square ≃ₜ Disc where
  toFun p := ⟨(2 * p.1 - 1, 2 * p.2 - 1), by
    rw [Prod.norm_mk, max_le_iff]
    obtain ⟨⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩ := p
    constructor <;> rw [Real.norm_eq_abs, abs_le] <;> constructor <;> dsimp <;> linarith⟩
  invFun p := (scaledCoord _ ((le_max_left _ _).trans p.property),
    scaledCoord _ ((le_max_right _ _).trans p.property))
  left_inv p := by
    ext <;> dsimp [scaledCoord] <;> ring
  right_inv p := by
    apply Subtype.ext
    ext <;> dsimp [scaledCoord] <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by unfold scaledCoord; fun_prop

private def planeAction (f : boundedPlane) : Square ≃ₜ Square :=
  (squareChart.trans (discAction f)).trans squareChart.symm

private def embedPlane : boundedPlane →* boundaryFixingHomeomorphisms where
  toFun f := ⟨planeAction f, by
    apply (mem_fixingSubgroup_iff _).mpr
    intro p hp
    have hn : ‖(squareChart p).val‖ = 1 := by
      apply le_antisymm (squareChart p).property
      change 1 ≤ max |2 * (p.1 : ℝ) - 1| |2 * (p.2 : ℝ) - 1|
      rcases hp with h | h | h | h <;> norm_num [h, le_max_iff]
    change squareChart.symm (extend f.val (squareChart p)) = p
    simp [extend, height, hn]⟩
  map_one' := by
    apply Subtype.ext
    ext p : 1
    change squareChart.symm (extend _ (squareChart p)) = p
    rw [← squareChart.symm_apply_apply p]
    congr 1
    generalize squareChart p = q
    obtain h | ⟨v, rfl⟩ := disc_cases q
    · simp [extend, h]
    · simp [extend_chart]
  map_mul' f g := by
    apply Subtype.ext
    ext p : 1
    change squareChart.symm (extend _ (squareChart p)) =
      squareChart.symm (extend _ (squareChart (squareChart.symm (extend _ (squareChart p)))))
    rw [squareChart.apply_symm_apply]
    congr 1
    obtain h | ⟨v, hv⟩ := disc_cases (squareChart p)
    · simp [extend, h]
    · simp [hv, extend_chart, Homeomorph.mul_apply]

private lemma embedPlane_injective : Function.Injective embedPlane := by
  intro f g h
  apply Subtype.ext
  ext v : 1
  have he := congrArg (fun k : boundaryFixingHomeomorphisms ↦
    squareChart (k.val (squareChart.symm (chart v)))) h
  change squareChart (squareChart.symm (extend _ (squareChart (squareChart.symm (chart v))))) =
    squareChart (squareChart.symm (extend _ (squareChart (squareChart.symm (chart v))))) at he
  simpa only [Homeomorph.apply_symm_apply, extend_chart, decode_chart] using congrArg decode he

/-! ### A periodic shear profile -/

-- In one period, warp fixes 0, 1/2 and 1 and takes 3/4 to 5/8, interpolating linearly.
-- Both corrections vanish at the endpoints, so they extend continuously across integers.
private def dent (r : ℝ) := max 0 (min ((r - 1 / 2) / 2) ((1 - r) / 2))

private def undent (r : ℝ) := max 0 (min (r - 1 / 2) ((1 - r) / 3))

private def warp (x : ℝ) := x - dent (Int.fract x)

private def unwarp (x : ℝ) := x + undent (Int.fract x)

private lemma fract_warp (x : ℝ) : Int.fract (warp x) = Int.fract x - dent (Int.fract x) := by
  rw [warp, sub_eq_add_neg, ← Int.fract_fract_add, Int.fract_eq_self.mpr]
  · rfl
  have h := Int.fract_nonneg x
  have h' := Int.fract_lt_one x
  unfold dent
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

private lemma fract_unwarp (x : ℝ) : Int.fract (unwarp x) = Int.fract x + undent (Int.fract x) := by
  rw [unwarp, ← Int.fract_fract_add, Int.fract_eq_self.mpr]
  have h := Int.fract_nonneg x
  have h' := Int.fract_lt_one x
  unfold undent
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

private lemma warp_unwarp (x : ℝ) : warp (unwarp x) = x := by
  rw [warp, fract_unwarp, unwarp]
  unfold dent undent
  simp only [max_def, min_def]
  split_ifs <;> linarith

private lemma unwarp_warp (x : ℝ) : unwarp (warp x) = x := by
  rw [unwarp, fract_warp, warp]
  unfold dent undent
  simp only [max_def, min_def]
  split_ifs <;> linarith

private lemma cont_warp : Continuous warp := by
  apply continuous_id.sub
  apply ContinuousOn.comp_fract'' (f := dent)
  · unfold dent; fun_prop
  · norm_num [dent]

private lemma cont_unwarp : Continuous unwarp := by
  apply continuous_id.add
  apply ContinuousOn.comp_fract'' (f := undent)
  · unfold undent; fun_prop
  · norm_num [undent]

private def step (x : ℝ) := unwarp (warp x + 1 / 2)

private def stepBack (x : ℝ) := unwarp (warp x - 1 / 2)

private lemma step_twice (x : ℝ) : step (step x) = x + 1 := by
  simp only [step, warp_unwarp]
  rw [show warp x + 1 / 2 + 1 / 2 = warp x + 1 by ring]
  calc
    unwarp (warp x + 1) = unwarp (warp x) + 1 := by simp [unwarp, add_right_comm]
    _ = x + 1 := by rw [unwarp_warp]

private lemma step_stepBack (x : ℝ) : step (stepBack x) = x := by
  simp [step, stepBack, warp_unwarp, unwarp_warp]

private lemma stepBack_step (x : ℝ) : stepBack (step x) = x := by
  simp [step, stepBack, warp_unwarp, unwarp_warp]

-- After reparametrization, the triangular wave takes the values 1, 0, -1, -1/2
-- at the quarter-period knots. Its four translates sum to -1/2 throughout the period.
private def tri (x : ℝ) := |4 * Int.fract x - 2| - 1

private def wave (x : ℝ) := tri (warp x)

private lemma cont_wave : Continuous wave := by
  apply Continuous.comp _ cont_warp
  apply ContinuousOn.comp_fract'' (f := fun t : ℝ ↦ |4 * t - 2| - 1)
  · fun_prop
  · norm_num

private lemma tri_neg (x : ℝ) : tri (x + 1 / 2) = -tri x := by
  have hl := Int.fract_nonneg x
  have hu := Int.fract_lt_one x
  unfold tri
  rw [← Int.fract_fract_add]
  by_cases h : Int.fract x < 1 / 2
  · rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
      abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    ring
  · rw [show Int.fract x + 1 / 2 = (Int.fract x - 1 / 2) + 1 by ring, Int.fract_add_one,
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
      abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    ring

private lemma wave_step (x : ℝ) : wave (step x) = -wave x := by
  simp only [wave, step, warp_unwarp, tri_neg]

private lemma wave_periodic : Function.Periodic wave 1 := by
  intro x
  simp [wave, tri, fract_warp]

private lemma wave_on {x : ℝ} (hl : 0 ≤ x) (hu : x < 1) :
    wave x = |4 * (x - dent x) - 2| - 1 := by
  simp [wave, tri, fract_warp, Int.fract_eq_self.mpr ⟨hl, hu⟩]

private def waveSum (x : ℝ) := wave x + wave (x + 1 / 4) + wave (x + 1 / 2) + wave (x + 3 / 4)

private lemma waveSum_periodic : Function.Periodic waveSum (1 / 4) := by
  intro x
  unfold waveSum
  rw [show x + 1 / 4 + 1 / 4 = x + 1 / 2 by ring,
      show x + 1 / 4 + 1 / 2 = x + 3 / 4 by ring,
      show x + 1 / 4 + 3 / 4 = x + 1 by ring, wave_periodic x]
  ring

private lemma waveSum_eq (x : ℝ) : waveSum x = -(1 / 2) := by
  suffices H : ∀ s : ℝ, 0 ≤ s → s < 1 / 4 → waveSum s = -(1 / 2) by
    rw [← waveSum_periodic.sub_zsmul_eq (x := x) ⌊4 * x⌋]
    simp only [zsmul_eq_mul]
    exact H _ (by linarith [Int.floor_le (4 * x)]) (by linarith [Int.lt_floor_add_one (4 * x)])
  intro s hl hu
  unfold waveSum
  rw [wave_on hl (by linarith), wave_on (by linarith : 0 ≤ s + 1 / 4) (by linarith),
      wave_on (by linarith : 0 ≤ s + 1 / 2) (by linarith),
      wave_on (by linarith : 0 ≤ s + 3 / 4) (by linarith)]
  have d0 : dent s = 0 := by unfold dent; exact max_eq_left ((min_le_left _ _).trans (by linarith))
  have d1 : dent (s + 1 / 4) = 0 := by
    unfold dent; exact max_eq_left ((min_le_left _ _).trans (by linarith))
  have d2 : dent (s + 1 / 2) = s / 2 := by
    unfold dent; rw [min_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have d3 : dent (s + 3 / 4) = (1 / 4 - s) / 2 := by
    unfold dent; rw [min_eq_right (by linarith), max_eq_right (by linarith)]; ring
  rw [d0, d1, d2, d3, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
    abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  ring

/-! ### Horizontal square roots and vertical translations -/

private def translatePlane (v : Plane) : boundedPlane :=
  ⟨Homeomorph.addRight v, ‖v‖, fun x ↦ by change ‖x + v - x‖ ≤ ‖v‖; simp⟩

private lemma translate_neg (v : Plane) : translatePlane (-v) = (translatePlane v)⁻¹ := by
  apply Subtype.ext
  ext p : 1
  change p + -v = p - v
  exact (sub_eq_add_neg _ _).symm

private lemma translate_pow (v : Plane) (n : ℕ) (p : Plane) :
    ((translatePlane v ^ n).val) p = p + n • v := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    change (translatePlane v ^ n).val (p + v) = _
    rw [ih, succ_nsmul]
    abel

private abbrev horiz := translatePlane (1, 0)

private abbrev vert (s : ℝ) := translatePlane (0, s)

private lemma vert_neg (s : ℝ) : vert (-s) = (vert s)⁻¹ := by
  simpa using translate_neg (0, s)

private lemma step_continuous : Continuous step :=
  cont_unwarp.comp (cont_warp.add continuous_const)

private lemma stepBack_continuous : Continuous stepBack :=
  cont_unwarp.comp (cont_warp.sub continuous_const)

attribute [local fun_prop] step_continuous stepBack_continuous cont_wave

/-- A conjugated horizontal half-translation with a vertical displacement.
The next half-step reverses the sign of that displacement, so its square translates by (1,0). -/
private def glideHomeo (i k : ℝ) : Plane ≃ₜ Plane where
  toFun p := (step (p.1 + i) - i, p.2 + k * wave (p.1 + i))
  invFun p := (stepBack (p.1 + i) - i, p.2 - k * wave (stepBack (p.1 + i)))
  left_inv p := by simp [stepBack_step]
  right_inv p := by simp [step_stepBack]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private lemma disp_periodic : Function.Periodic (fun x ↦ step x - x) 1 := by
  intro x
  have h (t : ℝ) : unwarp (t + 1) = unwarp t + 1 := by simp [unwarp, add_right_comm]
  have h' : warp (x + 1) = warp x + 1 := by simp [warp]; ring
  simp only [step, h', show warp x + 1 + 1 / 2 = (warp x + 1 / 2) + 1 by ring, h]
  ring

private def glide (i k : ℝ) : boundedPlane := ⟨glideHomeo i k, by
  obtain ⟨A, hA⟩ := isBounded_iff_forall_norm_le.mp
    (disp_periodic.isBounded_of_continuous one_ne_zero (step_continuous.sub continuous_id))
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp
    (wave_periodic.isBounded_of_continuous one_ne_zero cont_wave)
  refine ⟨max A (|k| * B), fun p ↦ ?_⟩
  change max |step (p.1 + i) - i - p.1| |p.2 + k * wave (p.1 + i) - p.2| ≤ _
  rw [sub_sub, add_comm i, add_sub_cancel_left, abs_mul]
  exact max_le_max (hA _ ⟨p.1 + i, rfl⟩) (mul_le_mul_of_nonneg_left (hB _ ⟨_, rfl⟩)
    (abs_nonneg _))⟩

private lemma glide_sq (i k : ℝ) : glide i k ^ 2 = horiz := by
  apply Subtype.ext
  ext p : 1
  change (step ((step (p.1 + i) - i) + i) - i,
    p.2 + k * wave (p.1 + i) + k * wave ((step (p.1 + i) - i) + i)) = (p.1 + 1, p.2 + 0)
  simp only [sub_add_cancel, step_twice, wave_step]
  congr 1 <;> ring

private lemma glide_commute (i k s : ℝ) : Commute (glide i k) (vert s) := by
  apply Subtype.ext
  ext p : 1
  change (step ((p.1 + 0) + i) - i, (p.2 + s) + k * wave ((p.1 + 0) + i)) =
    ((step (p.1 + i) - i) + 0, (p.2 + k * wave (p.1 + i)) + s)
  simp [add_right_comm]

-- Cancelling the horizontal half-step leaves just the vertical shear.
private def shearFactors (i k : ℝ) := [(glide i 0)⁻¹, glide i k]

private lemma shearFactors_apply (i k : ℝ) (p : Plane) : (shearFactors i k).prod.val p =
    (p.1, p.2 + k * wave (p.1 + i)) := by
  change (stepBack (step (p.1 + i) - i + i) - i,
    p.2 + k * wave (p.1 + i) - 0 * wave (stepBack (step (p.1 + i) - i + i))) = _
  simp [stepBack_step]

private lemma shearFactors_spec (i k s : ℝ) (g : boundedPlane) (hg : g ∈ shearFactors i k) :
    (g ^ 2 = horiz ∨ g ^ 2 = horiz⁻¹) ∧ Commute g (vert s) := by
  simp only [shearFactors, List.mem_cons, List.not_mem_nil, or_false] at hg
  obtain rfl | rfl := hg
  · exact ⟨Or.inr (by rw [inv_pow, glide_sq]), (glide_commute _ _ _).inv_left⟩
  · exact ⟨Or.inl (glide_sq _ _), glide_commute _ _ _⟩

/-- Four shears, one per quarter-period, translate every vertical line by the same amount. -/
private lemma vertical_factors (s : ℝ) : factors horiz (vert s) := by
  let k := -18 * s
  let l := shearFactors 0 k ++ (shearFactors (1 / 4) k ++
    (shearFactors (1 / 2) k ++ shearFactors (3 / 4) k))
  refine ⟨l, by change 8 < 9; decide, ?_, ?_⟩
  · apply Subtype.ext
    ext p : 1
    simp only [l, List.prod_append, Subgroup.coe_mul, Homeomorph.mul_apply, shearFactors_apply,
      translate_pow, Prod.smul_mk, nsmul_eq_mul]
    have h := waveSum_eq p.1
    simp only [waveSum] at h
    apply Prod.ext
    · simp
    · change _ = p.2 + 9 * s
      simp only [add_zero]
      dsimp only [k]
      linear_combination (-18 * s) * h
  · intro g hg
    simp only [l, List.mem_append] at hg
    rcases hg with hg | hg | hg | hg <;> exact shearFactors_spec _ _ _ _ hg

/-- Conjugation by the coordinate swap interchanges horizontal and vertical translations. -/
private def flipPlane : boundedPlane →* boundedPlane where
  toFun f := ⟨((Homeomorph.prodComm ℝ ℝ).trans f.val).trans (Homeomorph.prodComm ℝ ℝ), by
    obtain ⟨C, hC⟩ := f.property
    refine ⟨C, fun p ↦ ?_⟩
    change max ‖(f.val p.swap).2 - p.1‖ ‖(f.val p.swap).1 - p.2‖ ≤ C
    rw [max_comm]
    exact hC p.swap⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private lemma plane_no_order :
    ¬ ∃ s : boundedPlane → boundedPlane → Prop, IsLinearOrder _ s ∧
      ∀ a b c : boundedPlane, s a b → s (c * a) (c * b) := by
  have ha : horiz ≠ 1 := by
    intro h
    have := congrArg (fun f : boundedPlane ↦ (f.val 0).1) h
    norm_num [horiz, translatePlane, Homeomorph.addRight] at this
  have hb : vert 1 ≠ 1 := by
    intro h
    have := congrArg (fun f : boundedPlane ↦ (f.val 0).2) h
    norm_num [vert, translatePlane, Homeomorph.addRight] at this
  have hab := vertical_factors 1
  have habi : factors horiz (vert 1)⁻¹ := vert_neg 1 ▸ vertical_factors (-1)
  have H : flipPlane horiz = vert 1 := rfl
  have V : flipPlane (vert 1) = horiz := rfl
  apply exclude_order ha hb hab habi
  · simpa only [H, V] using factors_map flipPlane hab
  · simpa only [H, V, map_inv] using factors_map flipPlane habi

/--
**Boundary-fixing homeomorphisms of the disc are not right-orderable.** Let
$I^2 = [0, 1] \times [0, 1]$ be the closed square, a model of the closed disc, and let
$\mathrm{Homeo}(I^2; \partial I^2)$ be the group of homeomorphisms of $I^2$ that fix every point of
the boundary $\partial I^2$. There is no linear order $\le$ on $\mathrm{Homeo}(I^2; \partial I^2)$
such that $a \le b$ implies $ac \le bc$ for all $a, b, c$; that is, this group is not
right-orderable.

This answers Kourovka Problem 17.20 negatively: Hyde constructs a finitely generated subgroup of
$\mathrm{Homeo}(I^2; \partial I^2)$ that admits no left order, and left- and right-orderability
are equivalent via $g \mapsto g^{-1}$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory:
The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem
17.20 (G. M. Bergman); resolution: J. Hyde, The group of boundary fixing homeomorphisms of the disc
is not left-orderable, Ann. of Math. (2) 190 (2019), 657-661, abstract (a finitely generated
subgroup of Homeo(I²; ∂I²) admits no left order, hence neither does Homeo(I²; ∂I²)); Kourovka
Archive, Problem 17.20 (No, not always), https://annals.math.princeton.edu/2019/190-2/p05.
-/
theorem discBoundaryFixingHomeomorphismsRightOrderable_refuted :
    ¬ discBoundaryFixingHomeomorphismsRightOrderable :=
  reduceToSubgroup embedPlane embedPlane_injective plane_no_order

end

end MathlibExt.GroupTheory.BoundaryFixingHomeomorphismsOrderableKourovka17Problem20Wanted
