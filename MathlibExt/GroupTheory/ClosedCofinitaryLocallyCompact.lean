/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import MathlibExt.GroupTheory.Permutation.PointwiseTopology
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Div
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Closed cofinitary permutation groups need not be locally compact (Kourovka Notebook Problem 13.28)

Kourovka Notebook, Archive of Solved Problems, Problem 13.28 (D. M. Evans; P. J. Cameron): a
permutation group on an infinite set is cofinitary if its non-identity elements fix only finitely
many points. Is every closed cofinitary permutation group locally compact in the topology of
pointwise convergence?

The theorem `closedCofinitaryLocallyCompact_refuted` gives a counterexample using permutations
of the 2-adic integers. After doubling the coordinates, each permutation and its inverse agree
with a polynomial on every finite set. A polynomial fixing distinct doubled inputs has displacement
divisible by the product of the corresponding linear factors. This bounds the number of fixed
points of a nonidentity element. Polynomial perturbations fixing a prescribed finite set move
any further point through infinitely many values, ruling out compact identity neighborhoods.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.28 (D. M.
Evans; P. J. Cameron). UnsolvedMath record UM-00700946 (`KOU-13.28`), dataset ulamai/UnsolvedMath
v1.8.0.

The topology of pointwise convergence on `Sym(Ω)` is the shared `Equiv.Perm.pointwiseTopology`
(induced from the product `Ω → Ω` of discrete spaces); closed means closed in `Sym(Ω)`, and local
compactness refers to the subspace topology on `G`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.ClosedCofinitaryLocallyCompactKourovka13Problem28Wanted

/-- **Cofinitary permutation groups.** A subgroup $G$ of the group of permutations of a set
$\Omega$ is cofinitary when every non-identity element of $G$ fixes only finitely many points of
$\Omega$. -/
def IsCofinitary {Ω : Type} (G : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ g ∈ G, g ≠ 1 → {x : Ω | g x = x}.Finite

/-- **Claim of Kourovka Problem 13.28.** For every infinite set $\Omega$, every cofinitary subgroup
$G$ of the group of permutations of $\Omega$ that is closed in the topology of pointwise
convergence is locally compact in the subspace topology. -/
def closedCofinitaryLocallyCompact : Prop :=
  ∀ (Ω : Type) [Infinite Ω] (G : Subgroup (Equiv.Perm Ω)), IsCofinitary G →
    @IsClosed _ (Equiv.Perm.pointwiseTopology (α := Ω)) (G : Set (Equiv.Perm Ω)) →
    @LocallyCompactSpace G
      (TopologicalSpace.induced ((↑) : G → Equiv.Perm Ω)
        (Equiv.Perm.pointwiseTopology (α := Ω)))

open Polynomial
open scoped Topology

private abbrev R := ℤ_[2]

-- The factor of two puts all inputs in the same residue class. Each fixed point
-- will then contribute a factor of two to the displacement at any other point.
private def Interpolates (g : R → R) : Prop :=
  ∀ s : Finset R, ∃ P : R[X], ∀ x ∈ s, P.eval (2 * x) = 2 * g x

private lemma interpolates_comp {f g : R → R} (hf : Interpolates f) (hg : Interpolates g) :
    Interpolates (f ∘ g) := by
  classical
  intro s
  obtain ⟨P, hP⟩ := hg s
  obtain ⟨Q, hQ⟩ := hf (s.image g)
  exact ⟨Q.comp P, fun x hx ↦ by simp [eval_comp, hP x hx, hQ _ (Finset.mem_image_of_mem g hx)]⟩

private def group : Subgroup (Equiv.Perm R) where
  carrier := {g | Interpolates g ∧ Interpolates g.symm}
  one_mem' := by
    have h : Interpolates id := fun s ↦ ⟨X, fun _ _ ↦ eval_X⟩
    exact ⟨h, h⟩
  mul_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    exact ⟨interpolates_comp (f := ⇑f) (g := ⇑g) hf hg,
      interpolates_comp (f := ⇑g.symm) (g := ⇑f.symm) hg' hf'⟩
  inv_mem' := fun ⟨hf, hf'⟩ ↦ ⟨hf', hf⟩

-- Peel off the distinct linear factors contributed by the interpolation nodes.
private lemma nodes_dvd (s : Finset R) (a : R → R) (ha : Function.Injective a)
    (P : R[X]) (hP : ∀ i ∈ s, P.eval (a i) = 0) :
    (∏ i ∈ s, (X - C (a i))) ∣ P := by
  classical
  induction s using Finset.induction_on generalizing P with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨Q, rfl⟩ := dvd_iff_isRoot.mpr (hP i (Finset.mem_insert_self ..))
    rw [Finset.prod_insert hi]
    apply mul_dvd_mul_left
    apply ih
    intro j hj
    have hij : a j ≠ a i := fun h ↦ hi (ha h ▸ hj)
    simpa [sub_ne_zero.mpr hij] using hP j (Finset.mem_insert_of_mem hj)

private lemma double_injective : Function.Injective (fun x : R ↦ 2 * x) :=
  mul_right_injective₀ (by norm_num)

private lemma norm_two : ‖(2 : R)‖ = (1 / 2 : ℝ) := by
  simpa using PadicInt.norm_p (p := 2)

private lemma group_cofinitary : IsCofinitary group := by
  classical
  intro g hg hne
  by_contra hinf
  apply hne
  apply Equiv.ext
  intro x
  change g x = x
  by_contra hx
  have hd : 0 < ‖2 * g x - 2 * x‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr fun h ↦ hx (double_injective h))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hd (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf n
  obtain ⟨P, hP⟩ := hg.1 (insert x s)
  obtain ⟨Q, hQ⟩ := nodes_dvd s _ double_injective (P - X) (by
    intro i hi
    have hgi : g i = i := hs hi
    simp [hP i (Finset.mem_insert_of_mem hi), hgi])
  have he := congrArg (eval (2 * x)) hQ
  simp only [eval_sub, eval_X, hP x (Finset.mem_insert_self ..), eval_mul, eval_prod, eval_C] at he
  have hprod : (∏ i ∈ s, (2 * x - 2 * i)) = 2 ^ n * ∏ i ∈ s, (x - i) := by
    simp_rw [← mul_sub, Finset.prod_mul_distrib, Finset.prod_const, hcard]
  rw [he, hprod, mul_assoc, norm_mul, norm_pow, norm_two] at hn
  exact (not_lt_of_ge (mul_le_of_le_one_right (by positivity)
    (PadicInt.norm_le_one _))) hn

-- To invert a polynomial perturbation at y, solve x = y - P(2x) by contraction.
private lemma perturb_bijective (P : R[X]) :
    Function.Bijective (fun x : R ↦ x + P.eval (2 * x)) := by
  have contract (y : R) : ContractingWith (1 / 2) (fun x : R ↦ y - P.eval (2 * x)) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun a b ↦ ?_⟩
    obtain ⟨w, hw⟩ := sub_dvd_eval_sub (2 * b) (2 * a) P
    rw [dist_eq_norm, dist_eq_norm]
    have he : y - P.eval (2 * a) - (y - P.eval (2 * b)) = P.eval (2 * b) - P.eval (2 * a) := by
      abel
    rw [he, hw, ← mul_sub, norm_mul, norm_mul, norm_two, norm_sub_rev b a]
    simpa using mul_le_of_le_one_right (by positivity : 0 ≤ 1 / 2 * ‖a - b‖)
      (PadicInt.norm_le_one w)
  constructor
  · intro a b hab
    let y := a + P.eval (2 * a)
    apply (contract y).fixedPoint_unique'
    · change y - P.eval (2 * a) = a
      simp [y]
    · change y - P.eval (2 * b) = b
      exact sub_eq_iff_eq_add.mpr hab
  · intro y
    obtain ⟨x, hx⟩ : ∃ x, y - P.eval (2 * x) = x :=
      ⟨_, (contract y).fixedPoint_isFixedPt⟩
    exact ⟨x, (sub_eq_iff_eq_add.mp hx).symm⟩

private noncomputable def liftPoly (P : R[X]) : R[X] := X + C 2 * P

private lemma liftPoly_dvd (P : R[X]) (a b : R) :
    (liftPoly P).eval a - (liftPoly P).eval b ∣ a - b := by
  obtain ⟨w, hw⟩ := sub_dvd_eval_sub a b P
  have hlt : ‖2 * w‖ < 1 := by
    rw [norm_mul, norm_two]
    linarith [PadicInt.norm_le_one w]
  have hu : IsUnit (1 + 2 * w) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_add_eq_max_of_ne, norm_one, max_eq_left hlt.le]
    simpa using hlt.ne'
  have he : (liftPoly P).eval a - (liftPoly P).eval b = (a - b) * (1 + 2 * w) := by
    simp only [liftPoly, eval_add, eval_X, eval_mul, eval_C]
    linear_combination 2 * hw
  rw [he]
  simpa using mul_dvd_mul_left (a - b) (isUnit_iff_dvd_one.mp hu)

-- Interpolate the inverse on one more node by a Newton correction. Its denominator
-- divides the old interpolation error because the perturbation preserves differences up to units.
private lemma liftPoly_inverse (P : R[X]) (s : Finset R) :
    ∃ Q : R[X], ∀ x ∈ s, Q.eval ((liftPoly P).eval x) = x := by
  classical
  let F := liftPoly P
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s _ ih =>
    obtain ⟨Q, hQ⟩ := ih
    obtain ⟨B, hB⟩ := nodes_dvd s id Function.injective_id (X - Q.comp F) (by
      intro x hx
      simp [F, eval_comp, hQ x hx])
    have hd : (∏ i ∈ s, (F.eval a - F.eval i)) ∣ a - Q.eval (F.eval a) := by
      apply (Finset.prod_dvd_prod_of_dvd _ _ fun i _ ↦ liftPoly_dvd P a i).trans
      exact ⟨B.eval a, by simpa [eval_comp, eval_prod] using congrArg (eval a) hB⟩
    obtain ⟨c, hc⟩ := hd
    refine ⟨Q + (∏ i ∈ s, (X - C (F.eval i))) * C c, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simpa [F, add_comm, eval_prod] using (sub_eq_iff_eq_add.mp hc).symm
    · have hz : (∏ i ∈ s, (F.eval x - F.eval i)) = 0 :=
        Finset.prod_eq_zero hx (sub_self _)
      change (Q + _ * C c).eval (F.eval x) = x
      simpa only [eval_add, eval_mul, eval_prod, eval_sub, eval_X, eval_C, hz,
        zero_mul, add_zero] using hQ x hx

private noncomputable def perturb (P : R[X]) : Equiv.Perm R :=
  Equiv.ofBijective _ (perturb_bijective P)

private lemma perturb_mem (P : R[X]) : perturb P ∈ group := by
  classical
  have he (x : R) : (liftPoly P).eval (2 * x) = 2 * perturb P x := by
    change _ = 2 * (x + P.eval (2 * x))
    simp [liftPoly, mul_add]
  constructor
  · exact fun s ↦ ⟨liftPoly P, fun x _ ↦ he x⟩
  · intro s
    obtain ⟨Q, hQ⟩ := liftPoly_inverse P (s.image fun x ↦ 2 * (perturb P).symm x)
    refine ⟨Q, fun x hx ↦ ?_⟩
    simpa only [he, Equiv.apply_symm_apply] using
      hQ _ (Finset.mem_image_of_mem _ hx)

private lemma group_closed :
    @IsClosed _ (Equiv.Perm.pointwiseTopology (α := R)) (group : Set (Equiv.Perm R)) := by
  classical
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  let : TopologicalSpace (Equiv.Perm R) := Equiv.Perm.pointwiseTopology
  apply closure_subset_iff_isClosed.mp
  intro g hg
  have approx (s : Finset R) : ∃ f ∈ group, ∀ x ∈ s, f x = g x := by
    let U := (s : Set R).pi (fun i ↦ {g i})
    have hU : U ∈ 𝓝 (⇑g) := set_pi_mem_nhds s.finite_toSet fun _ _ ↦ by
      simp [nhds_discrete]
    obtain ⟨f, hf, hfg⟩ := mem_closure_iff_nhds.mp hg _ <|
      (mem_nhds_induced _ _ _).mpr ⟨U, hU, Set.Subset.rfl⟩
    exact ⟨f, hfg, hf⟩
  constructor
  · intro s
    obtain ⟨f, hf, he⟩ := approx s
    obtain ⟨P, hP⟩ := hf.1 s
    exact ⟨P, fun x hx ↦ by rw [← he x hx, hP x hx]⟩
  · intro s
    obtain ⟨f, hf, he⟩ := approx (s.image g.symm)
    obtain ⟨P, hP⟩ := hf.2 s
    refine ⟨P, fun x hx ↦ ?_⟩
    have hfx : f (g.symm x) = x := by
      simpa only [Equiv.apply_symm_apply] using he _ (Finset.mem_image_of_mem _ hx)
    rw [← f.symm_apply_eq.mpr hfx.symm, hP x hx]

-- The stabilizer of a finite set has an infinite orbit at any point outside the set.
private lemma stabilizer_infinite_orbit (s : Finset R) :
    ∃ a : R, (Set.range fun g : {g : group // ∀ i ∈ s, g.val i = i} ↦ g.val.val a).Infinite := by
  classical
  obtain ⟨a, -, ha⟩ := Set.infinite_univ.exists_notMem_finset s
  let P : R[X] := ∏ i ∈ s, (X - C (2 * i))
  have hv (x : R) : P.eval (2 * x) = ∏ i ∈ s, (2 * x - 2 * i) := by simp [P, eval_prod]
  have hPa : P.eval (2 * a) ≠ 0 := by
    rw [hv]
    exact Finset.prod_ne_zero_iff.mpr fun i hi ↦
      sub_ne_zero.mpr fun h ↦ ha (double_injective h ▸ hi)
  have hfix (c i : R) (hi : i ∈ s) : perturb (C c * P) i = i := by
    change i + (C c * P).eval (2 * i) = i
    have hz : (∏ j ∈ s, (2 * i - 2 * j)) = 0 := Finset.prod_eq_zero hi (sub_self _)
    simp [hv, hz]
  refine ⟨a, (Set.infinite_range_of_injective (f := fun c : R ↦ a + c * P.eval (2 * a))
    (fun _ _ h ↦ (mul_left_injective₀ hPa) (add_left_cancel h))).mono ?_⟩
  rintro _ ⟨c, rfl⟩
  refine ⟨⟨⟨perturb (C c * P), perturb_mem _⟩, hfix c⟩, ?_⟩
  change a + (C c * P).eval (2 * a) = _
  simp

private lemma group_not_locallyCompact :
    ¬ @LocallyCompactSpace group (TopologicalSpace.induced ((↑) : group → Equiv.Perm R)
      (Equiv.Perm.pointwiseTopology (α := R))) := by
  classical
  let : TopologicalSpace R := ⊥
  let : DiscreteTopology R := ⟨rfl⟩
  let : TopologicalSpace (Equiv.Perm R) := Equiv.Perm.pointwiseTopology
  intro h
  let : LocallyCompactSpace group := h
  obtain ⟨K, hK, hKmem⟩ := exists_compact_mem_nhds (1 : group)
  obtain ⟨V, hV, hVK⟩ := (mem_nhds_induced _ _ _).mp hKmem
  obtain ⟨U, hU, hUV⟩ := (mem_nhds_induced _ _ _).mp hV
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨s, t, ht, hsub⟩ := hU
  obtain ⟨a, ha⟩ := stabilizer_infinite_orbit s
  have hcont : Continuous (fun g : group ↦ g.val a) :=
    (continuous_apply a).comp (continuous_induced_dom.comp continuous_subtype_val)
  apply ha ((hK.image hcont).finite_of_discrete.subset ?_)
  rintro _ ⟨g, rfl⟩
  refine ⟨g.val, hVK (hUV (hsub ?_)), rfl⟩
  intro i hi
  change g.val.val i ∈ t i
  rw [g.property i hi]
  exact mem_of_mem_nhds (ht i)

/--
**Closed cofinitary permutation groups need not be locally compact.** The claim of Kourovka
Problem 13.28 is false: there are an infinite set $\Omega$ and a subgroup $G$ of the group of
permutations of $\Omega$ such that $G$ is cofinitary (every non-identity element of $G$ fixes only
finitely many points of $\Omega$) and closed in the topology of pointwise convergence, but $G$ is
not locally compact in the subspace topology.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.28 (D. M.
Evans; P. J. Cameron); resolution: G. Hjorth, J. Algebra 200 (1998), no. 2, 439-448, Kourovka
Archive, Problem 13.28: No, not always.
-/
theorem closedCofinitaryLocallyCompact_refuted : ¬ closedCofinitaryLocallyCompact :=
  fun h ↦ group_not_locallyCompact (h R group group_cofinitary group_closed)

end MathlibExt.GroupTheory.ClosedCofinitaryLocallyCompactKourovka13Problem28Wanted
