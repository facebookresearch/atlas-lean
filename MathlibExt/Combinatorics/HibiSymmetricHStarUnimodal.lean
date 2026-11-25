/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.WeightedProjectiveSimplexEhrhart
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.NatCard
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.IntervalCases

/-!
# A counterexample to Hibi's conjecture on symmetric $h^*$-vectors

The simplex with vertices $0$, $e_2,\ldots,e_6$ and $(9,-1,-1,-1,-1,-1)$ has
$h^*$-vector $(1,1,2,1,2,1,1)$. We compute its Ehrhart series by separating its lattice
points into nine residue classes.

This simplex occurs in Sam Payne, *Ehrhart series and lattice triangulations*, Example 4.2
with $(b,k,r)=(3,2,0)$. Translate by $f=(e_1+\cdots+e_6)/3$ and use the lattice basis
$f,e_2+f,\ldots,e_6+f$ to obtain the vertices above. <https://arxiv.org/abs/math/0702052>

## Record carried over from the retired wanted module

From `WantedExt/Combinatorics/HibiSymmetricHStarUnimodalOWR741Problem003Wanted.lean`:

Source: C. A. Athanasiadis, On the unimodality of h*-vectors, in Ehrhart Quasipolynomials: Algebra,
Combinatorics, and Geometry, Oberwolfach Reports 1 (2004), no. 39, p. 2078, Conjecture 2, DOI
10.4171/OWR/2004/39. UnsolvedMath record UM-30000109 (`OWR-741-003`), dataset ulamai/UnsolvedMath
v1.8.0.

A `d`-dimensional integral polytope is taken full-dimensional in `ℝ^d`, the convex hull of a finite
set of integer points with nonempty interior; every `d`-dimensional integral polytope is lattice
equivalent to one (and Mustaţă-Payne's polytope, a lattice polytope for the lattice `ℤ⁶ + ℤ f`,
becomes one in a basis of that lattice). The `h*`-polynomial is `MetaMathlibExt.IsHStarPolynomial`
(the source's identity `∑ i(P, r) t^r = h*(t) / (1 - t)^{d+1}`) and unimodality is
`MetaMathlibExt.IsUnimodal`, both reused from
`WantedExt.Combinatorics.WeightedProjectiveSimplexIDPWanted`. Conjecture 1 of the same abstract
(standard Gorenstein `R_P` implies unimodal `h*`) is already stated as
`conjectureGorensteinIDPUnimodal` in the OpenConjectures entry `IntegerDecompositionUnimodalHStar`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.HibiSymmetricHStarUnimodalOWR741Problem003Wanted

open MetaMathlibExt

/-- The lattice polytope in `ℝ^d` spanned by the finite set `S ⊆ ℤ^d` of integer points. -/
def latticePolytope {d : ℕ} (S : Finset (Fin d → ℤ)) : Set (Fin d → ℝ) :=
  convexHull ℝ ((fun v : Fin d → ℤ => fun i => (v i : ℝ)) '' (S : Set (Fin d → ℤ)))

/-- **Hibi's conjecture on symmetric $h^*$-vectors.** For every natural number $d$, every finite
set $S \subseteq \mathbb{Z}^d$ whose convex hull $P \subseteq \mathbb{R}^d$ has nonempty interior,
and every polynomial $h = \sum_i h^*_i z^i \in \mathbb{Z}[z]$ that is an $h^*$-polynomial of $P$,
that is,
$$\Big(\sum_{t \ge 0} \#(tP \cap \mathbb{Z}^d)\, z^t\Big) (1 - z)^{d+1} = h(z)$$
as formal power series, if $h^*_i = h^*_{d-i}$ for all $0 \le i \le d$, then $h$ is unimodal.

This is Hibi's conjecture, Conjecture 2 of C. A. Athanasiadis's Oberwolfach report (Oberwolfach
Reports 1 (2004), no. 39, p. 2078), stated there for $d$-dimensional integral polytopes; every
such polytope is lattice-equivalent to a full-dimensional lattice polytope in $\mathbb{R}^d$. -/
def hibiSymmetricUnimodal : Prop :=
  ∀ (d : ℕ) (S : Finset (Fin d → ℤ)), (interior (latticePolytope S)).Nonempty →
    ∀ h : Polynomial ℤ, IsHStarPolynomial (latticePolytope S) h →
      (∀ i ≤ d, h.coeff i = h.coeff (d - i)) → IsUnimodal h

-- For a lattice point the six barycentric coordinates opposite the nonzero vertices
-- have the same fractional part, determined by its first coordinate modulo nine.
private def project {R : Type*} [Ring R] (w : Fin 6 → R) : Fin 6 → R :=
  Fin.cons (9 * w 0) (fun i => w i.succ - w 0)

private noncomputable def bary (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  Fin.cons (x 0 / 9) (fun i => x i.succ + x 0 / 9)

private theorem bary_project (w : Fin 6 → ℝ) : bary (project w) = w := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [bary, project]

private theorem project_bary (x : Fin 6 → ℝ) : project (bary x) = x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [bary, project]
  ring

private def projectMap : (Fin 7 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun w := project (fun i => w i.succ)
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [project] <;> ring
  map_smul' a x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [project] <;> ring

private def vertices : Finset (Fin 6 → ℤ) :=
  Finset.univ.image (fun j : Fin 7 => project (fun i => (Pi.single j 1 : Fin 7 → ℤ) i.succ))

private theorem hull_basis :
    convexHull ℝ (Set.range fun j : Fin 7 => (Pi.single j 1 : Fin 7 → ℝ)) =
      {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
  ext w
  constructor
  · rw [convexHull_range_eq_exists_affineCombination]
    rintro ⟨s, f, h, hs, rfl⟩
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hs]
    suffices ∀ i, 0 ≤ (if i ∈ s then f i else 0) by
      simpa [Finset.sum_apply, Pi.single_apply, mul_ite, hs] using this
    intro i
    split_ifs with hi
    · exact h i hi
    · exact le_rfl
  · rintro ⟨h, hs⟩
    apply mem_convexHull_of_exists_fintype w _ h hs (fun i => Set.mem_range_self i)
    ext i
    simp [Finset.sum_apply, Pi.single_apply, mul_ite]

private theorem polytope_eq_image :
    latticePolytope vertices = projectMap '' {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
  rw [← hull_basis, projectMap.image_convexHull,
    ← Set.range_comp', latticePolytope, vertices, Finset.coe_image, Finset.coe_univ,
    Set.image_univ, ← Set.range_comp']
  congr 1
  apply congrArg Set.range
  funext j i
  refine Fin.cases ?_ (fun k => ?_) i <;> simp [projectMap, project, Pi.single_apply]

private theorem mem_polytope (x : Fin 6 → ℝ) :
    x ∈ latticePolytope vertices ↔ (∀ i, 0 ≤ bary x i) ∧ ∑ i, bary x i ≤ 1 := by
  rw [polytope_eq_image]
  constructor
  · rintro ⟨w, ⟨hw, hs⟩, rfl⟩
    change (∀ i, 0 ≤ bary (project fun i => w i.succ) i) ∧ _
    simp only [show projectMap w = project (fun i => w i.succ) from rfl, bary_project]
    rw [Fin.sum_univ_succ] at hs
    exact ⟨fun i => hw i.succ, by linarith [hw 0]⟩
  · rintro ⟨hw, hs⟩
    refine ⟨Fin.cons (1 - ∑ i, bary x i) (bary x), ⟨?_, ?_⟩, ?_⟩
    · intro i
      exact Fin.cases (by simpa using hs) (fun i => by simpa using hw i) i
    · simp [Fin.sum_univ_succ (n := 6)]
    · simpa [projectMap] using project_bary x

private theorem interior_nonempty : (interior (latticePolytope vertices)).Nonempty := by
  let U := {x : Fin 6 → ℝ | (∀ i, 0 < bary x i) ∧ ∑ i, bary x i < 1}
  have hc (i : Fin 6) : Continuous (fun x => bary x i) := by
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp only [bary, Fin.cons_zero, Fin.cons_succ] <;> fun_prop
  have hopen : IsOpen U := by
    simp only [U, Set.ofPred_and, Set.ofPred_forall]
    exact (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (hc i)).inter
      (isOpen_lt (continuous_finsetSum _ fun i _ => hc i) continuous_const)
  refine ⟨project (fun _ => 1 / 9), interior_maximal (t := U) (fun x hx => (mem_polytope x).2
    ⟨fun i => (hx.1 i).le, hx.2.le⟩) hopen ?_⟩
  simp [U, bary_project]
  norm_num

private theorem bary_scale (a : ℝ) (x : Fin 6 → ℝ) (i : Fin 6) :
    bary (fun j => a * x j) i = a * bary x i := by
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [bary] <;> ring

private theorem mem_dilate (t : ℕ) (x : Fin 6 → ℝ) :
    x ∈ polytopeDilate t (latticePolytope vertices) ↔
      (∀ i, 0 ≤ bary x i) ∧ ∑ i, bary x i ≤ t := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h, hs⟩ := (mem_polytope y).1 hy
    simp only [bary_scale, ← Finset.mul_sum]
    exact ⟨fun i => mul_nonneg (by positivity) (h i), by nlinarith [Nat.cast_nonneg (α := ℝ) t]⟩
  · rintro ⟨h, hs⟩
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · have hz : ∑ i, bary x i = 0 :=
        le_antisymm (by simpa using hs) (Finset.sum_nonneg fun i _ => h i)
      have hx : bary x = 0 := funext fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => h j).1 hz i (Finset.mem_univ _)
      refine ⟨x, (mem_polytope x).2 ⟨h, by simp [hx]⟩, ?_⟩
      rw [← project_bary x, hx]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [project]
    · have ht' : (0 : ℝ) < t := by exact_mod_cast ht
      refine ⟨fun i => (t : ℝ)⁻¹ * x i, (mem_polytope _).2 ?_, ?_⟩
      · simp only [bary_scale, ← Finset.mul_sum]
        exact ⟨fun i => mul_nonneg (by positivity) (h i), (inv_mul_le_iff₀ ht').2 (by simpa)⟩
      · ext i
        simp [ht'.ne']

-- Euclidean division of the first coordinate gives a residue and six integer parts.
private def latticeCoords : (Fin 9 × (Fin 6 → ℤ)) ≃ (Fin 6 → ℤ) where
  toFun p := Fin.cons (9 * p.2 0 + p.1.val) (fun i => p.2 i.succ - p.2 0)
  invFun x := (⟨((x 0) % 9).toNat, by omega⟩,
    Fin.cons (x 0 / 9) (fun i => x i.succ + x 0 / 9))
  left_inv := by
    rintro ⟨r, z⟩
    apply Prod.ext
    · apply Fin.ext
      simp only [Fin.cons_zero]
      omega
    · ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp <;> omega
  right_inv x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
    omega

-- The sum of the six fractional parts is 6r/9, so the first integral dilate
-- containing the residue class r is at height ⌈2r/3⌉.
private def height (r : Fin 9) : ℕ := (2 * r.val + 2) / 3

private theorem mem_latticeCoords (r : Fin 9) (z : Fin 6 → ℤ) (t : ℕ) :
    IsLatticePoint (polytopeDilate t (latticePolytope vertices)) (latticeCoords (r, z)) ↔
      (∀ i, 0 ≤ z i) ∧ ∑ i, z i + (height r : ℤ) ≤ t := by
  have he (i : Fin 6) :
      bary (fun j => (latticeCoords (r, z) j : ℝ)) i = z i + (r.val : ℝ) / 9 := by
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [bary, latticeCoords] <;> ring
  rw [IsLatticePoint, mem_dilate]
  simp only [he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Int.cast_sum]
  refine and_congr (forall_congr' fun i => ?_) ?_
  · have h : 0 ≤ (z i : ℝ) + r.val / 9 ↔ (0 : ℝ) ≤ 9 * z i + r.val := by
      constructor <;> intro h <;> linarith
    rw [h]
    exact_mod_cast (show (0 : ℤ) ≤ 9 * z i + r.val ↔ 0 ≤ z i by omega)
  · have h : (↑(∑ i, z i) : ℝ) + 6 * ((r.val : ℝ) / 9) ≤ t ↔
        3 * (↑(∑ i, z i) : ℝ) + 2 * r.val ≤ 3 * t := by
      constructor <;> intro h <;> linarith
    norm_num only [Nat.cast_ofNat] at *
    rw [h]
    exact_mod_cast (show (3 : ℤ) * (∑ i, z i) + 2 * r.val ≤ 3 * t ↔
      (∑ i, z i) + (height r : ℤ) ≤ t by unfold height; omega)

private abbrev Parts (r : Fin 9) (t : ℕ) :=
  {b : Fin 6 → ℕ // (∑ i, b i) + height r ≤ t}

private noncomputable def pointEquiv (t : ℕ) :
    (Σ r, Parts r t) ≃ {x // IsLatticePoint (polytopeDilate t (latticePolytope vertices)) x} :=
  Equiv.ofBijective
    (fun p => ⟨latticeCoords (p.1, fun i => (p.2.val i : ℤ)),
      (mem_latticeCoords ..).2 ⟨fun _ => by positivity, by exact_mod_cast p.2.property⟩⟩) (by
      constructor
      · rintro ⟨r, b⟩ ⟨s, c⟩ he
        have h := latticeCoords.injective (Subtype.mk.inj he)
        obtain rfl : r = s := congrArg Prod.fst h
        congr 2
        ext i
        exact Int.ofNat_inj.mp (congrFun (congrArg Prod.snd h) i)
      · rintro ⟨x, hx⟩
        obtain ⟨⟨r, z⟩, rfl⟩ := latticeCoords.surjective x
        obtain ⟨hn, hs⟩ := (mem_latticeCoords ..).1 hx
        have hz (i) : ((z i).toNat : ℤ) = z i := Int.toNat_of_nonneg (hn i)
        refine ⟨⟨r, ⟨fun i => (z i).toNat, ?_⟩⟩, Subtype.ext ?_⟩
        · exact_mod_cast (show (∑ i, ((z i).toNat : ℤ)) + (height r : ℤ) ≤ t by simpa [hz])
        · exact congrArg (fun w => latticeCoords (r, w)) (funext hz))

-- The unused barycentric weight is the slack variable in stars and bars.
private def slackEquiv {r : Fin 9} {t : ℕ} (hr : height r ≤ t) :
    Parts r t ≃ {b : Fin 7 → ℕ // ∑ i, b i = t - height r} where
  toFun b := ⟨Fin.cons (t - height r - ∑ i, b.val i) b.val, by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hb := b.property
    omega⟩
  invFun b := ⟨fun i => b.val i.succ, by
    dsimp only
    have hb := b.property
    rw [Fin.sum_univ_succ] at hb
    omega⟩
  left_inv b := by ext; simp
  right_inv b := by
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      have hb := b.property
      rw [Fin.sum_univ_succ] at hb
      omega
    · simp

private noncomputable def partsEquivSym {r : Fin 9} {t : ℕ} (hr : height r ≤ t) :
    Parts r t ≃ Sym (Fin 7) (t - height r) :=
  (slackEquiv hr).trans (Sym.equivNatSumOfFintype ..).symm

private theorem parts_empty {r : Fin 9} {t : ℕ} (hr : ¬ height r ≤ t) : IsEmpty (Parts r t) :=
  ⟨fun b => hr ((Nat.le_add_left ..).trans b.property)⟩

private theorem ehrhart_count (t : ℕ) :
    ehrhart (latticePolytope vertices) t =
      ∑ r : Fin 9, if height r ≤ t then (6 + (t - height r)).choose 6 else 0 := by
  have (r : Fin 9) : Finite (Parts r t) := by
    by_cases hr : height r ≤ t
    · exact Finite.of_equiv _ (partsEquivSym hr).symm
    · have := parts_empty hr
      infer_instance
  change Nat.card {x // IsLatticePoint (polytopeDilate t (latticePolytope vertices)) x} = _
  rw [← Nat.card_congr (pointEquiv t), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs with hr
  · rw [Nat.card_congr (partsEquivSym hr), Sym.natCard_sym_eq_choose, Nat.card_fin]
    rw [show 7 + (t - height r) - 1 = 6 + (t - height r) by omega, Nat.choose_symm_add]
  · have := parts_empty hr
    exact Nat.card_of_isEmpty

private noncomputable def numerator : Polynomial ℤ := ∑ r : Fin 9, Polynomial.X ^ height r

private theorem isHStar : IsHStarPolynomial (latticePolytope vertices) numerator := by
  let G := (PowerSeries.invOneSubPow ℤ 7).val
  have hgen : PowerSeries.mk (fun t => (ehrhart (latticePolytope vertices) t : ℤ)) =
      G * (numerator : PowerSeries ℤ) := by
    ext t
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, numerator, map_sum]
    have hG : G = PowerSeries.mk (fun n => ((6 + n).choose 6 : ℤ)) := rfl
    simp only [PowerSeries.coeff_mk, ehrhart_count, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_pow, Polynomial.coe_X,
      Finset.mul_sum, map_sum, PowerSeries.coeff_mul_X_pow', hG]
  unfold IsHStarPolynomial
  rw [hgen, mul_comm G, mul_assoc, Fintype.card_fin]
  change (numerator : PowerSeries ℤ) * (_ * (1 - PowerSeries.X) ^ 7) = _
  rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow ℤ 7, Units.val_inv, mul_one]

private theorem coefficients :
    ∀ k : Fin 7, numerator.coeff k.val = ![1, 1, 2, 1, 2, 1, 1] k := by
  simp only [numerator, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
  decide

/--
**Hibi's conjecture on symmetric $h^*$-vectors is false.** There are a natural number $d$, a
finite set $S \subseteq \mathbb{Z}^d$ whose convex hull $P \subseteq \mathbb{R}^d$ has nonempty
interior, and a polynomial $h = \sum_i h^*_i z^i \in \mathbb{Z}[z]$ that is an $h^*$-polynomial
of $P$, that is,
$$\Big(\sum_{t \ge 0} \#(tP \cap \mathbb{Z}^d)\, z^t\Big) (1 - z)^{d+1} = h(z)$$
as formal power series, such that $h^*_i = h^*_{d-i}$ for all $0 \le i \le d$ but $h$ is not
unimodal.

Mustaţă and Payne (Example 1.1) give a reflexive $6$-dimensional lattice polytope with
$h^*$-vector $(1, 6, 8, 6, 8, 6, 1)$, which is symmetric and not unimodal.

Source: C. A. Athanasiadis, On the unimodality of h*-vectors, in Ehrhart Quasipolynomials: Algebra,
Combinatorics, and Geometry, Oberwolfach Reports 1 (2004), no. 39, p. 2078, Conjecture 2, DOI
10.4171/OWR/2004/39; resolution: M. Mustaţă and S. Payne, Ehrhart polynomials and stringy Betti
numbers, Math. Ann. 333 (2005), 787-795, DOI 10.1007/s00208-005-0691-x, arXiv:math/0504486, Example
1.1: for f = (e1 + ... + e6)/3, N = ℤ⁶ + ℤ f and P the polytope with vertices e1, ..., e6, e1 - f,
..., e6 - f, P is reflexive with δ_P = (1, 6, 8, 6, 8, 6, 1), a counterexample to Hibi's conjecture
for d = 6 (abstract: 'counterexamples to Hibi's conjecture on the unimodality of delta-vectors of
reflexive polytopes'), https://arxiv.org/abs/math/0504486.
-/
public theorem hibiSymmetricUnimodal_refuted : ¬ hibiSymmetricUnimodal := by
  intro h
  have hsym (i : ℕ) (hi : i ≤ 6) : numerator.coeff i = numerator.coeff (6 - i) := by
    rw [coefficients ⟨i, by omega⟩, coefficients ⟨6 - i, by omega⟩]
    interval_cases i <;> rfl
  obtain ⟨t, _, hle, hge⟩ := h 6 vertices interior_nonempty numerator isHStar hsym
  have h₂ : numerator.coeff 2 = 2 := coefficients 2
  have h₃ : numerator.coeff 3 = 1 := coefficients 3
  have h₄ : numerator.coeff 4 = 2 := coefficients 4
  by_cases ht : 3 ≤ t
  · have := hle 2 3 (by decide) ht
    omega
  · have hd : 4 ≤ numerator.natDegree := Polynomial.le_natDegree_of_ne_zero (by omega)
    have := hge 3 4 (by omega) (by decide) hd
    omega

end MathlibExt.Combinatorics.HibiSymmetricHStarUnimodalOWR741Problem003Wanted
