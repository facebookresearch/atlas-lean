/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.AvoidanceCoreDimGe3
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.HeightCut.ConeCutAvoidance
import Appendix_FixedPoint.BezoutChain.Dimension.HeightLowerBound
import Appendix_FixedPoint.BezoutChain.Dimension.PolynomialCatenary
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.Data.ENat.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Order.WithBot
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Nullstellensatz

/-!
# R-B2: general-`n` A3a (`z ∈ Q`) closer + dim-kit

The E10 `hA3a` binder
(`AvoidanceCoreDimGe3.minAvoidNonprimeSpec_of_zClosers`) at general
`n ≥ 3` — the A3a closer `ZMemAvoidCloser` ∀-form from per-realized
`(hexp, hN, htower, hcomm, [IsAlgClosed K])`, no `horth`, no
diagonality, no ∀-forms — plus the A2(iii) `x`-ideal exclusion and the
dim-kit it consumes.

## Route (contraction-free)

The design note's §C sketches an A3a route via contraction to `K[x]` (dim-kit
D1). The assembly below does not contract: working directly in the
bridge ring `R = K[x, z]`, the count is strictly better
(`height(P') ≤ n - 1 < n + 1`, no `j.val ≥ 2` load), so D1
(`contraction_height_le_of_free`) is unneeded and not stated here.
Per fixed `(j, Q)` with `z ∈ Q` and contra-hypothesis `q_j ∈ Q`:
`Q ⊇ (q_0, …, q_j, z)`; cut by the remaining `n - 1 - j.val` forms
(D3) to `P' ∈ Min(Q ⊔ span{cuts})`; `P'` has height `≤ n - 1`
(D3 + banked A2(i)); hence `V(P')` holds a nonzero point (D4);
that point kills all of `bridgeSystem` and `z`, so the `hN` engine
(RB3's general-`n` `hN_contra_of_cone_point`, D5 by reuse) closes the
contra. Generalize over `Q`, then `j`, to feed E10's `hA3a` binder.

## Residual register (exact)

Proved here (zero placeholders): D2 quotient-dim (`quot_dim_ge_of_height_le`),
D4 nonzero point (`exists_ne_zero_mem_zeroLocus_of_height_le`),
properness of the cut (`cutIdeal_ne_top_of_mem_minimalPrimes`),
the D3 quotient-kht half inside `height_le_of_mem_minimalPrimes_cut`,
A2(iii) (`xIdeal_notMem_minimalPrimes_stageIdeal`), and the A3a
assembly (`bridgeNotMem_zMem_of_algebraData`,
`zMemAvoidCloser_of_algebraData`).

* `HeightCutAdditivity` (D3 gap): for primes `Q ≤ P'` in
  `MvPolynomial (Fin (t+2)) K`,
  `height(P') ≤ height(Q) + height(P'/Q)` — the catenary consequence
  whose proof needs going-down for the normalization (same gap as RB3's
  open `hcut`, which this additivity also closes: `hcut` is the
  principal case at `n = 3`). Threaded as `hadd`.
* D1 contraction-height lift: not needed (contraction-free route above).
* A1 `z`-span exclusion: skipped, logically subsumed by A3a (design note §A:
  "Do A1 last or not at all").

Conditional on exactly `[HeightCutAdditivity]` given algebra data
+ `[IsAlgClosed K]` (tagged `[algClosed]` at use sites).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace A3aCloserDimKit

open scoped BigOperators

/-! ## §D2. Quotient dimension from the height cap -/

/-- Quotient dimension (D2, general vars): `dim(R/Q) ≥ d` from
`height(Q) ≤ k` with `k + d = t + 2`, via the unconditional catenary
equality `height + dim = t + 2` (`hlow_uncond` +
`mvPolynomial_catenary_eq_of_lower_bound`) and ENat cancellation
(RB3's `dim_ge_of_height_add_dim_eq`). Generalizes RB3's
`quot_dim_ge_two` (`n = 3`) to general `t`. [algClosed] -/
theorem quot_dim_ge_of_height_le (t : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (Q : Ideal (MvPolynomial (Fin (t + 2)) K)) [Q.IsPrime]
    (k d : ℕ) (hadd : k + d = t + 2) (hle : Q.height ≤ ((k : ℕ) : ℕ∞)) :
    ((((d : ℕ)) : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin (t + 2)) K ⧸ Q) := by
  have hlow := hlow_uncond t K Q
  have hcat := mvPolynomial_catenary_eq_of_lower_bound K (t + 2) Q hlow
  have hle' : (Q.height : WithBot ℕ∞) ≤ ((((k : ℕ)) : ℕ∞) : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr hle
  have hcat' : (Q.height : WithBot ℕ∞) +
      ringKrullDim (MvPolynomial (Fin (t + 2)) K ⧸ Q)
      = ((((t + 2 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
    have hRHS : (((t + 2 : ℕ)) : WithBot ℕ∞)
        = ((((t + 2 : ℕ)) : ℕ∞) : WithBot ℕ∞) :=
      (WithBot.coe_natCast (t + 2)).symm
    rw [hRHS] at hcat
    exact hcat
  exact ConeCutAvoidance.dim_ge_of_height_add_dim_eq _ _ k d (t + 2) hadd hcat' hle'

#print axioms quot_dim_ge_of_height_le

/-! ## §D4. Nonzero points on positive-dimensional varieties -/

/-- Weak Nullstellensatz (D4a, general vars): the zero locus of a proper
ideal is nonempty — via `vanishingIdeal_zeroLocus_eq_radical` and
`radical_eq_top`. Generalizes RB3's `zeroLocus_nonempty_of_ne_top`
(`n = 3`). [algClosed] -/
theorem zeroLocus_nonempty_of_ne_top_gen (t : ℕ) (K : Type*) [Field K] [IsAlgClosed K]
    (I : Ideal (MvPolynomial (Fin (t + 2)) K))
    (hI : I ≠ ⊤) :
    MvPolynomial.zeroLocus K I ≠ ∅ := by
  intro hempty
  have hvan := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) I
  rw [hempty] at hvan
  rw [MvPolynomial.vanishingIdeal_empty] at hvan
  have htop : I.radical = ⊤ := hvan.symm
  rw [Ideal.radical_eq_top] at htop
  exact hI htop

#print axioms zeroLocus_nonempty_of_ne_top_gen

/-- The vanishing ideal of the origin is maximal (Mathlib
instance, general vars). -/
theorem isMaximal_vanishingIdeal_singleton_zero_gen (t : ℕ) (K : Type*) [Field K] :
    (MvPolynomial.vanishingIdeal K
      ({0} : Set (Fin (t + 2) → K)) :
      Ideal (MvPolynomial (Fin (t + 2)) K)).IsMaximal :=
  inferInstance

#print axioms isMaximal_vanishingIdeal_singleton_zero_gen

/-- No low-height component is the origin (D4b, general vars): if
`V(P') = {0}` then `P'` is the irrelevant maximal ideal, of height
`t + 2` — against `height(P') ≤ t + 1`. Generalizes RB3's
`zeroLocus_ne_singleton_zero_of_height_le_three`. [algClosed] -/
theorem zeroLocus_ne_singleton_zero_of_height_le (t : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (P' : Ideal (MvPolynomial (Fin (t + 2)) K))
    [P'.IsPrime] (h3 : P'.height ≤ ((t + 1 : ℕ) : ℕ∞)) :
    MvPolynomial.zeroLocus K P' ≠ {0} := by
  intro hcon
  have hprime : P'.IsPrime := inferInstance
  have hP' : P' = (MvPolynomial.vanishingIdeal K
      ({0} : Set (Fin (t + 2) → K)) :
      Ideal (MvPolynomial (Fin (t + 2)) K)) := by
    have hvan := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) P'
    rw [hcon] at hvan
    have hrad : P'.radical = P' := hprime.radical
    rw [hrad] at hvan
    exact hvan.symm
  have hmax : P'.IsMaximal := by
    rw [hP']
    exact isMaximal_vanishingIdeal_singleton_zero_gen t K
  have h4 := @height_maximal_ge t K _ _ P' hmax
  have hle : ((((t + 2 : ℕ))) : ℕ∞) ≤ ((((t + 1 : ℕ))) : ℕ∞) := le_trans h4 h3
  have hcon' : ¬ ((((t + 2 : ℕ))) : ℕ∞) ≤ ((((t + 1 : ℕ))) : ℕ∞) := by
    intro h
    have hnm : t + 2 ≤ t + 1 := by exact_mod_cast h
    omega
  exact absurd hle hcon'

#print axioms zeroLocus_ne_singleton_zero_of_height_le

/-- A prime of height `≤ t + 1` in `t + 2` variables has a nonzero zero
(D4c, general vars): `V(P') ≠ ∅` (D4a) and `V(P') ≠ {0}` (D4b) force a
nonzero point. Generalizes RB3's
`exists_ne_zero_mem_zeroLocus_of_height_le_three`. [algClosed] -/
theorem exists_ne_zero_mem_zeroLocus_of_height_le (t : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K]
    (P' : Ideal (MvPolynomial (Fin (t + 2)) K))
    [P'.IsPrime] (h3 : P'.height ≤ ((t + 1 : ℕ) : ℕ∞)) :
    ∃ a ∈ MvPolynomial.zeroLocus K P', a ≠ 0 := by
  have hprime : P'.IsPrime := inferInstance
  have hne : MvPolynomial.zeroLocus K P' ≠ ∅ := by
    apply zeroLocus_nonempty_of_ne_top_gen t K P'
    exact hprime.ne_top
  have hns : MvPolynomial.zeroLocus K P' ≠ {0} :=
    @zeroLocus_ne_singleton_zero_of_height_le t K _ _ P' hprime h3
  by_contra hall
  have hall' : ∀ a ∈ MvPolynomial.zeroLocus K P', a = 0 := by
    intro a ha
    by_contra hne'
    exact hall ⟨a, ha, hne'⟩
  have hsub : MvPolynomial.zeroLocus K P' ⊆ {0} := by
    intro a ha
    simp only [Set.mem_singleton_iff]
    exact hall' a ha
  have hsup : ({0} : Set (Fin (t + 2) → K)) ⊆
      MvPolynomial.zeroLocus K P' := by
    intro a ha
    simp only [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hb0 := hall' b hb
    rw [← hb0]
    exact hb
  exact hns (Set.Subset.antisymm hsub hsup)

#print axioms exists_ne_zero_mem_zeroLocus_of_height_le

/-! ## §R1-gen. Stage ideals are homogeneous; the cut is proper -/

/-- Stage ideals are homogeneous (general `n`): every homogeneous
component of a member is a member (`span_induction` with universal
motive; generators are homogeneous of degree 2). Generalizes RB3's
`stageIdeal2_homog_mem` (`n = 3`). -/
theorem stageIdeal_homog_mem (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) :
    ∀ x ∈ MinAvoidRungs.stageIdeal n K c hn j, ∀ i,
      MvPolynomial.homogeneousComponent i x ∈ MinAvoidRungs.stageIdeal n K c hn j := by
  intro x hx
  have hx' : x ∈ Submodule.span (MvPolynomial (Fin (statementIndex n + 2)) K)
      (Set.image (bridgeSystem n K c hn) {k | k.val < j.val}) := hx
  refine Submodule.span_induction (p := fun x _ => ∀ i,
      MvPolynomial.homogeneousComponent i x ∈ MinAvoidRungs.stageIdeal n K c hn j) ?_ ?_ ?_ ?_ hx'
  · intro y hy
    show ∀ i, MvPolynomial.homogeneousComponent i y ∈ MinAvoidRungs.stageIdeal n K c hn j
    intro i
    obtain ⟨k, hk, rfl⟩ := hy
    have hhom : ((bridgeSystem n K c hn) k).IsHomogeneous 2 :=
      bridgeSystem_homogeneous n K c hn k
    have hmem2 : (bridgeSystem n K c hn) k ∈
        MvPolynomial.homogeneousSubmodule (Fin (statementIndex n + 2)) K 2 :=
      (MvPolynomial.mem_homogeneousSubmodule 2 ((bridgeSystem n K c hn) k)).mpr hhom
    have hif : MvPolynomial.homogeneousComponent i ((bridgeSystem n K c hn) k) =
        (if i = 2 then (bridgeSystem n K c hn) k else 0) :=
      MvPolynomial.homogeneousComponent_of_mem hmem2
    rw [hif]
    by_cases hii : i = 2
    · rw [ite_eq_left hii]
      exact Ideal.subset_span ⟨k, hk, rfl⟩
    · rw [ite_eq_right hii]
      exact (MinAvoidRungs.stageIdeal n K c hn j).zero_mem
  · change ∀ i, MvPolynomial.homogeneousComponent i
        (0 : MvPolynomial (Fin (statementIndex n + 2)) K) ∈
        MinAvoidRungs.stageIdeal n K c hn j
    intro i
    rw [map_zero]
    exact (MinAvoidRungs.stageIdeal n K c hn j).zero_mem
  · intro a b _ha _hb iha ihb
    change ∀ i, MvPolynomial.homogeneousComponent i (a + b) ∈
      MinAvoidRungs.stageIdeal n K c hn j
    intro i
    rw [map_add]
    exact (MinAvoidRungs.stageIdeal n K c hn j).add_mem (iha i) (ihb i)
  · intro r y _hy ih
    change ∀ i, MvPolynomial.homogeneousComponent i (r • y) ∈
      MinAvoidRungs.stageIdeal n K c hn j
    intro i
    rw [smul_eq_mul, ConeCutAvoidance.hc_mul_expand r y i]
    exact Ideal.sum_mem (MinAvoidRungs.stageIdeal n K c hn j) (fun p _hp => by
      change (if i = p.1 + p.2 then MvPolynomial.homogeneousComponent p.1 r *
          MvPolynomial.homogeneousComponent p.2 y else
          (0 : MvPolynomial (Fin (statementIndex n + 2)) K)) ∈
          MinAvoidRungs.stageIdeal n K c hn j
      by_cases hif : i = p.1 + p.2
      · rw [ite_eq_left hif]
        exact Ideal.mul_mem_left (MinAvoidRungs.stageIdeal n K c hn j) _ (ih p.2)
      · rw [ite_eq_right hif]
        exact (MinAvoidRungs.stageIdeal n K c hn j).zero_mem)

#print axioms stageIdeal_homog_mem

/-- A homogeneous-of-degree-2 polynomial lies in the irrelevant ideal:
every support monomial has total degree 2, hence a nonzero component. -/
theorem homogQuad_mem_irrelevant {σ : Type*} {K : Type*} [Field K]
    (g : MvPolynomial σ K) (hhom : g.IsHomogeneous 2) :
    g ∈ Ideal.span (MvPolynomial.X '' Set.univ) := by
  rw [MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have h2 : 2 = ∑ i ∈ m.support, m i :=
    MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hhom hm
  by_contra hall
  have h0 : ∀ i, m i = 0 := by
    intro i
    by_contra hi
    exact hall ⟨i, Set.mem_univ i, hi⟩
  have hsum0 : ∑ i ∈ m.support, m i = 0 :=
    Finset.sum_eq_zero (fun i _ => h0 i)
  omega

#print axioms homogQuad_mem_irrelevant

/-- Properness (general `n`, general homogeneous cuts): `Q ⊔ span(cuts) ≠ ⊤`
for `Q ∈ Min(J_j)` — minimality forces `Q = homCore Q` (RB3's
`homCore_prime`), hence `Q` is homogeneous, hence below the proper
irrelevant ideal; the cuts join it there. Generalizes RB3's
`hproper_homog` (`n = 3`, cuts `= {z}`). -/
theorem cutIdeal_ne_top_of_mem_minimalPrimes (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1))
    (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hQ : Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes)
    (cuts : Finset (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hcuts : ∀ g ∈ cuts, g.IsHomogeneous 2) :
    Q ⊔ Ideal.span (↑cuts : Set (MvPolynomial (Fin (statementIndex n + 2)) K)) ≠ ⊤ := by
  have hprime : Q.IsPrime := hQ.isPrime
  have hmin : (MinAvoidRungs.stageIdeal n K c hn j).IsMinimalPrime Q := hQ
  have hHCprime : (ConeCutAvoidance.homCore Q).IsPrime :=
    ConeCutAvoidance.homCore_prime Q hprime
  have hHCQ : ConeCutAvoidance.homCore Q ≤ Q := ConeCutAvoidance.homCore_le Q
  have hJHC : MinAvoidRungs.stageIdeal n K c hn j ≤ ConeCutAvoidance.homCore Q := by
    intro x hx i
    exact hQ.le (stageIdeal_homog_mem n K c hn j x hx i)
  obtain ⟨_unused, hmin2⟩ := hmin
  have hQleHC : Q ≤ ConeCutAvoidance.homCore Q := hmin2 ⟨hHCprime, hJHC⟩ hHCQ
  have hHeq : ConeCutAvoidance.homCore Q = Q := le_antisymm hHCQ hQleHC
  have hQhom : ∀ x ∈ Q, ∀ i,
      MvPolynomial.homogeneousComponent i x ∈ Q := by
    intro x hx i
    have hxHC : x ∈ ConeCutAvoidance.homCore Q := by
      rw [hHeq]
      exact hx
    exact hxHC i
  have hQsub : Q ≤ Ideal.span (MvPolynomial.X '' Set.univ) :=
    ConeCutAvoidance.homogPrime_le_span_X Q hprime hQhom
  have hcutsSub : Ideal.span (↑cuts : Set (MvPolynomial (Fin (statementIndex n + 2)) K))
      ≤ Ideal.span (MvPolynomial.X '' Set.univ) := by
    refine Ideal.span_le.mpr ?_
    intro y hy
    exact homogQuad_mem_irrelevant y (hcuts y (Finset.mem_coe.mp hy))
  have h1notin : (1 : MvPolynomial (Fin (statementIndex n + 2)) K) ∉
      Ideal.span (MvPolynomial.X '' Set.univ) := by
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro hall
    have h0mem : (0 : Fin (statementIndex n + 2) →₀ ℕ) ∈
        (1 : MvPolynomial (Fin (statementIndex n + 2)) K).support := by
      rw [MvPolynomial.support_one]
      exact Finset.mem_singleton_self 0
    obtain ⟨i, _univ, hi⟩ := hall 0 h0mem
    rw [Finsupp.zero_apply] at hi
    exact hi rfl
  have hspan_ne : Ideal.span (MvPolynomial.X '' Set.univ :
      Set (MvPolynomial (Fin (statementIndex n + 2)) K)) ≠ ⊤ :=
    (Ideal.ne_top_iff_one _).mpr h1notin
  have hle : Q ⊔ Ideal.span (↑cuts : Set (MvPolynomial (Fin (statementIndex n + 2)) K)) ≤
      Ideal.span (MvPolynomial.X '' Set.univ) :=
    sup_le hQsub hcutsSub
  intro hcon
  rw [hcon] at hle
  exact hspan_ne (top_le_iff.mp hle)

#print axioms cutIdeal_ne_top_of_mem_minimalPrimes

/-! ## §D3. The principal-cut height bound (conditional on additivity) -/

/-- Height additivity under containment (D3 gap, open): for primes
`Q ≤ P'` in `MvPolynomial (Fin (t+2)) K`, `height(P')` is at most
`height(Q)` plus the height of the image prime `P'/Q`. This standard
catenary consequence is the exact gap: its proof needs going-down for
the normalization (same gap as RB3's open `hcut`, which this additivity
closes as its principal case at `n = 3`: `height(P') ≤ 2 + 1 = 3`).

Status: open-residual (definition naming it). -/
def HeightCutAdditivity (t : ℕ) (K : Type*) [Field K] : Prop :=
  ∀ (Q P' : Ideal (MvPolynomial (Fin (t + 2)) K)),
    Q.IsPrime → P'.IsPrime → Q ≤ P' →
      P'.height ≤ Q.height + (Ideal.map (Ideal.Quotient.mk Q) P').height

#print axioms HeightCutAdditivity

/-- PIT-cut (D3): `P' ∈ Min(Q ⊔ span{cuts})` has
`height(P') ≤ height(Q) + cuts.card`, from the additivity gap plus the
quotient-side Krull height theorem (`height_le_ncard_of_mem_minimalPrimes_span`):
the image prime `P'/Q` is minimal over the cut images (descent via a
minimal prime below + pullback), hence of height `≤ cuts.card`.

Conditional on exactly `[HeightCutAdditivity]`. -/
theorem height_le_of_mem_minimalPrimes_cut (t : ℕ) (K : Type*) [Field K]
    (Q P' : Ideal (MvPolynomial (Fin (t + 2)) K))
    [Q.IsPrime] [P'.IsPrime]
    (cuts : Finset (MvPolynomial (Fin (t + 2)) K))
    (hP' : P' ∈ (Q ⊔ Ideal.span (↑cuts : Set (MvPolynomial (Fin (t + 2)) K))).minimalPrimes)
    (hadd : HeightCutAdditivity t K) :
    P'.height ≤ Q.height + ((cuts.card : ℕ) : ℕ∞) := by
  have hle : Q ⊔ Ideal.span (↑cuts : Set (MvPolynomial (Fin (t + 2)) K)) ≤ P' := hP'.le
  have hQP : Q ≤ P' := le_trans le_sup_left hle
  have hPbar : (Ideal.map (Ideal.Quotient.mk Q) P').IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hQP
  have hspan_le : Ideal.span (Ideal.Quotient.mk Q '' (↑cuts : Set (MvPolynomial (Fin (t + 2)) K)))
      ≤ Ideal.map (Ideal.Quotient.mk Q) P' := by
    refine Ideal.span_le.mpr ?_
    intro y hy
    obtain ⟨g, hg, rfl⟩ := hy
    rw [SetLike.mem_coe,
      Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective]
    refine ⟨g, ?_, rfl⟩
    apply hle
    exact Ideal.mem_sup_right (Ideal.subset_span (Finset.mem_coe.mpr hg))
  obtain ⟨p0, hp0min, hp0le⟩ :=
    @Ideal.exists_minimalPrimes_le _ _ _ _ hPbar hspan_le
  have hsfin : (Ideal.Quotient.mk Q '' (↑cuts : Set (MvPolynomial (Fin (t + 2)) K))).Finite :=
    (Finset.finite_toSet cuts).image _
  have hp0KHT := Ideal.height_le_ncard_of_mem_minimalPrimes_span hsfin hp0min
  have hcard : (Ideal.Quotient.mk Q '' (↑cuts : Set (MvPolynomial (Fin (t + 2)) K))).ncard
      ≤ cuts.card := by
    have h1 := Set.ncard_image_le (f := Ideal.Quotient.mk Q)
      (s := (↑cuts : Set (MvPolynomial (Fin (t + 2)) K))) (Finset.finite_toSet cuts)
    rw [Set.ncard_coe_finset] at h1
    exact h1
  have hp0card : p0.height ≤ ((cuts.card : ℕ) : ℕ∞) :=
    le_trans hp0KHT (by exact_mod_cast hcard)
  have hp0prime : p0.IsPrime := hp0min.isPrime
  have hpull_prime : (Ideal.comap (Ideal.Quotient.mk Q) p0).IsPrime :=
    hp0prime.comap (Ideal.Quotient.mk Q)
  have hpull_ge : Q ⊔ Ideal.span (↑cuts : Set (MvPolynomial (Fin (t + 2)) K))
      ≤ Ideal.comap (Ideal.Quotient.mk Q) p0 := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [Ideal.mem_comap]
      have hzx : Ideal.Quotient.mk Q x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
      rw [hzx]
      exact p0.zero_mem
    · refine Ideal.span_le.mpr ?_
      intro g hg
      rw [SetLike.mem_coe, Ideal.mem_comap]
      apply hp0min.le
      exact Ideal.subset_span ⟨g, Finset.mem_coe.mp hg, rfl⟩
  have hpull_le : Ideal.comap (Ideal.Quotient.mk Q) p0 ≤ P' := by
    intro x hx
    rw [Ideal.mem_comap] at hx
    have hx2 : Ideal.Quotient.mk Q x ∈ Ideal.map (Ideal.Quotient.mk Q) P' :=
      hp0le hx
    rw [Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk Q)
      Ideal.Quotient.mk_surjective] at hx2
    obtain ⟨y, hyP, hyx⟩ := hx2
    have hsub : y - x ∈ Q := (Ideal.Quotient.mk_eq_mk_iff_sub_mem y x).mp hyx
    have hyx' : x = y - (y - x) := by abel
    rw [hyx']
    exact P'.sub_mem hyP (hQP hsub)
  obtain ⟨_u, hmin2⟩ := hP'
  have hP'ge : P' ≤ Ideal.comap (Ideal.Quotient.mk Q) p0 :=
    hmin2 ⟨hpull_prime, hpull_ge⟩ hpull_le
  have hP'eq : Ideal.comap (Ideal.Quotient.mk Q) p0 = P' :=
    le_antisymm hpull_le hP'ge
  have hbar_eq : Ideal.map (Ideal.Quotient.mk Q) P' = p0 := by
    have hmc := Ideal.map_comap_of_surjective (Ideal.Quotient.mk Q)
      Ideal.Quotient.mk_surjective p0
    rw [hP'eq] at hmc
    exact hmc
  have hadd2 := hadd Q P' inferInstance inferInstance hQP
  rw [hbar_eq] at hadd2
  exact le_trans hadd2 (by gcongr)

#print axioms height_le_of_mem_minimalPrimes_cut

/-! ## §A3a. The `z ∈ Q` closer -/

/-- Count of rungs above `j`: `#{k : Fin m | jv < k.val} ≤ m - (jv + 1)`,
via the injective valuation map into `Ico (jv + 1) m`. -/
theorem card_filter_gt (m : ℕ) (jv : ℕ) (_hj : jv < m) :
    (Finset.filter (fun k : Fin m => jv < k.val) Finset.univ).card ≤ m - (jv + 1) := by
  have hval_inj : Function.Injective (fun k : Fin m => k.val) := fun _ _ hab => Fin.ext hab
  have hcard : (Finset.image (fun k : Fin m => k.val)
        (Finset.filter (fun k : Fin m => jv < k.val) Finset.univ)).card
      = (Finset.filter (fun k : Fin m => jv < k.val) Finset.univ).card :=
    Finset.card_image_of_injective _ hval_inj
  have hsub : Finset.image (fun k : Fin m => k.val)
        (Finset.filter (fun k : Fin m => jv < k.val) Finset.univ)
      ⊆ Finset.Ico (jv + 1) m := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [Finset.mem_Ico]
    exact ⟨Nat.succ_le_of_lt hk, k.isLt⟩
  calc (Finset.filter (fun k : Fin m => jv < k.val) Finset.univ).card
        = (Finset.image (fun k : Fin m => k.val)
          (Finset.filter (fun k : Fin m => jv < k.val) Finset.univ)).card := hcard.symm
      _ ≤ (Finset.Ico (jv + 1) m).card := Finset.card_le_card hsub
      _ = m - (jv + 1) := Nat.card_Ico _ _

#print axioms card_filter_gt

/-- A3a per-`(j, Q)` form (headline, per-rung): at fixed nonprime rung `j`
and `Q ∈ Min(J_j)` with `z ∈ Q`, the rung element avoids `Q` — from
algebra data + `[IsAlgClosed K]` + the D3 additivity gap. The
contra-hypothesis `q_j ∈ Q` puts all of `(q_0, …, q_j, z)` in `Q`; the
D3 cut by the remaining forms yields `P'` of height `≤
statementIndex n + 1` (i.e. `≤ n` by `shift_add_one`, matching
the proved `h3`); D4 gives
a nonzero point killing all of `bridgeSystem` and `z`; D5
(`hN_contra_of_cone_point`, reused) contradicts `hN`. The `2 ≤ j.val`
binder is carried for address compatibility with E10's `hA3a`
(the contraction-free count needs no lower bound on `j`). [algClosed]

Conditional on exactly `[HeightCutAdditivity]` given algebra data. -/
theorem bridgeNotMem_zMem_of_algebraData
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    [IsScalarTower K E E] [SMulCommClass K E E]
    (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (j : Fin (statementIndex n + 1)) (_hj : 2 ≤ j.val)
    (Q : Ideal (MvPolynomial (Fin (statementIndex n + 2)) K))
    (hQmin : Q ∈ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes)
    (hz : AvoidanceCoreDimGe3.zVarPoly n K ∈ Q)
    (hadd : HeightCutAdditivity (statementIndex n) K) :
    (bridgeSystem n K c hn) j ∉ Q := by
  classical
  set cuts : Finset (MvPolynomial (Fin (statementIndex n + 2)) K) :=
    Finset.image (bridgeSystem n K c hn)
      (Finset.filter (fun k => j.val < k.val) Finset.univ) with hcuts
  have hcuts_hom : ∀ g ∈ cuts, g.IsHomogeneous 2 := by
    intro g hg
    rw [hcuts, Finset.mem_image] at hg
    obtain ⟨k, _hk, rfl⟩ := hg
    exact bridgeSystem_homogeneous n K c hn k
  have hproper := cutIdeal_ne_top_of_mem_minimalPrimes n K c hn j Q hQmin cuts hcuts_hom
  obtain ⟨P', hP'⟩ := Ideal.nonempty_minimalPrimes hproper
  have hQprime : Q.IsPrime := hQmin.isPrime
  have hP'prime : P'.IsPrime := hP'.isPrime
  have hP3 := @height_le_of_mem_minimalPrimes_cut (statementIndex n) K _ Q P'
    hQprime hP'prime cuts hP' hadd
  have hcap := AvoidanceCoreDimGe3.height_le_of_mem_minimalPrimes_stageIdeal
    n K c hn j Q hQmin
  have hflt : (Finset.filter (fun k : Fin (statementIndex n + 1) => j.val < k.val)
        Finset.univ).card
      ≤ (statementIndex n + 1) - (j.val + 1) :=
    card_filter_gt _ _ j.isLt
  have hcard : cuts.card ≤ (statementIndex n + 1) - (j.val + 1) := by
    rw [hcuts]
    exact le_trans Finset.card_image_le hflt
  have h3 : P'.height ≤ (((statementIndex n + 1 : ℕ)) : ℕ∞) := by
    refine le_trans hP3 ?_
    have hmono : Q.height + ((cuts.card : ℕ) : ℕ∞)
        ≤ ((j.val : ℕ) : ℕ∞)
          + ((((statementIndex n + 1) - (j.val + 1) : ℕ)) : ℕ∞) :=
      add_le_add hcap (by exact_mod_cast hcard)
    refine le_trans hmono ?_
    have harith : j.val + ((statementIndex n + 1) - (j.val + 1)) ≤ statementIndex n + 1 := by
      have hjlt := j.isLt
      omega
    have hcast : ((j.val : ℕ) : ℕ∞) + ((((statementIndex n + 1) - (j.val + 1) : ℕ)) : ℕ∞)
        = ((((j.val + ((statementIndex n + 1) - (j.val + 1))) : ℕ)) : ℕ∞) :=
      (Nat.cast_add _ _).symm
    rw [hcast]
    exact_mod_cast harith
  obtain ⟨a, haV, hane⟩ := @exists_ne_zero_mem_zeroLocus_of_height_le
    (statementIndex n) K _ _ P' hP'prime h3
  have haV' : a ∈ MvPolynomial.zeroLocus K
      (Q ⊔ Ideal.span (↑cuts : Set (MvPolynomial (Fin (statementIndex n + 2)) K))) :=
    MvPolynomial.zeroLocus_anti_mono hP'.le haV
  by_contra hcon
  have hz_mem : AvoidanceCoreDimGe3.zVarPoly n K
      ∈ Q ⊔ Ideal.span (↑cuts : Set (MvPolynomial (Fin (statementIndex n + 2)) K)) :=
    Ideal.mem_sup_left hz
  have hz_eval : a (Fin.last (statementIndex n + 1)) = 0 := by
    have ha0 := haV'
    rw [MvPolynomial.mem_zeroLocus_iff] at ha0
    have heval := ha0 _ hz_mem
    simp only [AvoidanceCoreDimGe3.zVarPoly] at heval
    rw [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_X] at heval
    exact heval
  have hGall : ∀ k : Fin (statementIndex n + 1),
      MvPolynomial.eval a ((bridgeSystem n K c hn) k) = 0 := by
    intro k
    have ha0 := haV'
    rw [MvPolynomial.mem_zeroLocus_iff] at ha0
    have hmemQ : (bridgeSystem n K c hn) k
        ∈ Q ⊔ Ideal.span (↑cuts : Set (MvPolynomial (Fin (statementIndex n + 2)) K)) := by
      by_cases hk : k.val < j.val
      · apply Ideal.mem_sup_left
        apply hQmin.le
        exact Ideal.subset_span ⟨k, hk, rfl⟩
      · by_cases hkj : k.val = j.val
        · apply Ideal.mem_sup_left
          have hkj' : k = j := Fin.ext hkj
          rw [hkj']
          exact hcon
        · apply Ideal.mem_sup_right
          apply Ideal.subset_span
          rw [hcuts, Finset.mem_coe, Finset.mem_image]
          refine ⟨k, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
    have hev := ha0 _ hmemQ
    rw [MvPolynomial.aeval_eq_eval] at hev
    exact hev
  exact ConeCutAvoidance.hN_contra_of_cone_point n K E V c b hexp hN hn a hane hz_eval hGall

#print axioms bridgeNotMem_zMem_of_algebraData

/-- A3a ∀-form (headline): the E10 `hA3a` binder
(`minAvoidNonprimeSpec_of_zClosers`) — every nonprime rung `j`
`z`-close-avoids — from algebra data + `[IsAlgClosed K]` + the D3
additivity gap. Feeding this (with R-B3's A3b lane) upgrades the E10 T3
headline to `[A3b, halloc]`-conditional at general `n`. [algClosed]

Conditional on exactly `[HeightCutAdditivity]` given algebra data. -/
theorem zMemAvoidCloser_of_algebraData
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    [IsScalarTower K E E] [SMulCommClass K E E]
    (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E) = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (hadd : HeightCutAdditivity (statementIndex n) K) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      AvoidanceCoreDimGe3.ZMemAvoidCloser n K c hn j := by
  intro j hj _hnp Q hQmin hz
  exact bridgeNotMem_zMem_of_algebraData K E n hn c V b hexp hN j hj Q hQmin hz hadd

#print axioms zMemAvoidCloser_of_algebraData

/-! ## §A2(iii). The `x`-ideal exclusion -/

/-- Initial-segment variable ideal: span of `X (castSucc i)` for
`i.val < k`. `xSegIdeal n K 0 = ⊥`; `xSegIdeal n K n` is the full
`x`-ideal `(x_0, …, x_{n-1})`. -/
noncomputable def xSegIdeal (n : ℕ) (K : Type*) [Field K] (k : ℕ) :
    Ideal (MvPolynomial (Fin (statementIndex n + 2)) K) :=
  Ideal.span (Set.image (fun i : Fin (statementIndex n + 1) => MvPolynomial.X (Fin.castSucc i))
    {i | i.val < k})

#print axioms xSegIdeal

/-- Kill the first `k` `x`-variables: `X (castSucc j) ↦ 0` for
`j.val < k`, all other variables fixed. -/
noncomputable def killHom (n : ℕ) (K : Type*) [Field K] (k : ℕ) :
    MvPolynomial (Fin (statementIndex n + 2)) K →+* MvPolynomial (Fin (statementIndex n + 2)) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i =>
    if i ∈ Finset.image (Fin.castSucc : Fin (statementIndex n + 1) → Fin (statementIndex n + 2))
      (Finset.filter (fun j : Fin (statementIndex n + 1) => j.val < k) Finset.univ)
    then 0 else MvPolynomial.X i)

#print axioms killHom

/-- `killHom` on variables: the defining if. -/
theorem killHom_X (n : ℕ) (K : Type*) [Field K] (k : ℕ) (i : Fin (statementIndex n + 2)) :
    killHom n K k (MvPolynomial.X i) =
    (if i ∈ Finset.image (Fin.castSucc : Fin (statementIndex n + 1) → Fin (statementIndex n + 2))
      (Finset.filter (fun j : Fin (statementIndex n + 1) => j.val < k) Finset.univ)
    then (0 : MvPolynomial (Fin (statementIndex n + 2)) K) else MvPolynomial.X i) :=
  MvPolynomial.eval₂Hom_X' _ _ _

#print axioms killHom_X

/-- `killHom` fixes constants. -/
theorem killHom_C (n : ℕ) (K : Type*) [Field K] (k : ℕ) (a : K) :
    killHom n K k (MvPolynomial.C a) = MvPolynomial.C a :=
  MvPolynomial.eval₂Hom_C _ _ _

#print axioms killHom_C

/-- The crux: `f - killHom f` always lies in the segment ideal
(induction: constants cancel, sums split, and
`(p * X i) - kill(p) * kill(X i)` is either `p * X i` (killed `i`)
or `(p - kill p) * X i` (fixed `i)`). -/
theorem sub_killHom_mem_xSegIdeal (n : ℕ) (K : Type*) [Field K] (k : ℕ)
    (f : MvPolynomial (Fin (statementIndex n + 2)) K) :
    f - killHom n K k f ∈ xSegIdeal n K k := by
  induction f using MvPolynomial.induction_on with
  | C a =>
      rw [killHom_C, sub_self]
      exact (xSegIdeal n K k).zero_mem
  | add p q hp hq =>
      have hmap : killHom n K k (p + q) = killHom n K k p + killHom n K k q :=
        map_add _ _ _
      rw [hmap]
      have halg : p + q - (killHom n K k p + killHom n K k q)
          = (p - killHom n K k p) + (q - killHom n K k q) := by abel
      rw [halg]
      exact (xSegIdeal n K k).add_mem hp hq
  | mul_X p i hp =>
      have hmap : killHom n K k (p * MvPolynomial.X i)
          = killHom n K k p * killHom n K k (MvPolynomial.X i) := map_mul _ _ _
      rw [hmap, killHom_X]
      by_cases hi : i ∈ Finset.image
          (Fin.castSucc : Fin (statementIndex n + 1) → Fin (statementIndex n + 2))
          (Finset.filter (fun j : Fin (statementIndex n + 1) => j.val < k) Finset.univ)
      · rw [ite_eq_left hi, mul_zero, sub_zero]
        obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp hi
        have hjval : j.val < k := (Finset.mem_filter.mp hj).2
        have hXi : MvPolynomial.X i ∈ xSegIdeal n K k := by
          rw [← hjeq]
          unfold xSegIdeal
          exact Ideal.subset_span ⟨j, hjval, rfl⟩
        exact Ideal.mul_mem_left _ _ hXi
      · rw [ite_eq_right hi]
        have halg : p * MvPolynomial.X i - killHom n K k p * MvPolynomial.X i
            = (p - killHom n K k p) * MvPolynomial.X i := by ring
        rw [halg]
        exact Ideal.mul_mem_right _ _ hp

#print axioms sub_killHom_mem_xSegIdeal

/-- The segment ideal is exactly the kill kernel (⊇: the kill map
vanishes on generators; ⊆: the crux above). -/
theorem xSegIdeal_eq_ker_killHom (n : ℕ) (K : Type*) [Field K] (k : ℕ) :
    xSegIdeal n K k = RingHom.ker (killHom n K k) := by
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    intro y hy
    obtain ⟨j, hjval, rfl⟩ := hy
    change MvPolynomial.X (Fin.castSucc j) ∈ RingHom.ker (killHom n K k)
    rw [RingHom.mem_ker, killHom_X]
    have hjval' : j.val < k := hjval
    have hkill : Fin.castSucc j ∈ Finset.image
        (Fin.castSucc : Fin (statementIndex n + 1) → Fin (statementIndex n + 2))
        (Finset.filter (fun j : Fin (statementIndex n + 1) => j.val < k) Finset.univ) :=
      Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjval'⟩, rfl⟩
    rw [ite_eq_left hkill]
  · intro f hf
    rw [RingHom.mem_ker] at hf
    have hsub := sub_killHom_mem_xSegIdeal n K k f
    rw [hf, sub_zero] at hsub
    exact hsub

#print axioms xSegIdeal_eq_ker_killHom

/-- Segment ideals are prime (kernels into a domain). -/
theorem xSegIdeal_isPrime (n : ℕ) (K : Type*) [Field K] (k : ℕ) :
    (xSegIdeal n K k).IsPrime := by
  rw [xSegIdeal_eq_ker_killHom]
  exact RingHom.ker_isPrime (killHom n K k)

#print axioms xSegIdeal_isPrime

/-- Segments grow with `k`. -/
theorem xSegIdeal_le_succ (n : ℕ) (K : Type*) [Field K] (k : ℕ) :
    xSegIdeal n K k ≤ xSegIdeal n K (k + 1) := by
  unfold xSegIdeal
  refine Ideal.span_le.mpr ?_
  intro y hy
  obtain ⟨i, hi, rfl⟩ := hy
  exact Ideal.subset_span ⟨i, lt_trans hi (Nat.lt_succ_self k), rfl⟩

#print axioms xSegIdeal_le_succ

/-- Segments grow strictly below the variable count: `X_k` enters at
step `k + 1` but is fixed (hence nonzero) under `killHom k`. -/
theorem xSegIdeal_lt_succ (n : ℕ) (K : Type*) [Field K] (k : ℕ)
    (hk : k < statementIndex n + 1) :
    xSegIdeal n K k < xSegIdeal n K (k + 1) := by
  refine lt_of_le_of_ne (xSegIdeal_le_succ n K k) ?_
  intro hcon
  have hmem : MvPolynomial.X (Fin.castSucc (⟨k, hk⟩ : Fin (statementIndex n + 1)))
      ∈ xSegIdeal n K (k + 1) := by
    unfold xSegIdeal
    exact Ideal.subset_span ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩
  rw [← hcon] at hmem
  have hnkilled : Fin.castSucc (⟨k, hk⟩ : Fin (statementIndex n + 1)) ∉ Finset.image
      (Fin.castSucc : Fin (statementIndex n + 1) → Fin (statementIndex n + 2))
      (Finset.filter (fun j : Fin (statementIndex n + 1) => j.val < k) Finset.univ) := by
    intro hcon2
    obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp hcon2
    have hjval : j.val < k := (Finset.mem_filter.mp hj).2
    have hjk : j = (⟨k, hk⟩ : Fin (statementIndex n + 1)) :=
      Fin.castSucc_injective _ hjeq
    have hval : j.val = k := congrArg Fin.val hjk
    omega
  have hXne : (MvPolynomial.X (Fin.castSucc (⟨k, hk⟩ : Fin (statementIndex n + 1))) :
      MvPolynomial (Fin (statementIndex n + 2)) K) ≠ 0 := by
    intro hzero
    have hev := congrArg
      (MvPolynomial.eval (fun _ : Fin (statementIndex n + 2) => (1 : K))) hzero
    simp only [MvPolynomial.eval_X, map_zero] at hev
    exact one_ne_zero hev
  have hnot : MvPolynomial.X (Fin.castSucc (⟨k, hk⟩ : Fin (statementIndex n + 1)))
      ∉ xSegIdeal n K k := by
    rw [xSegIdeal_eq_ker_killHom, RingHom.mem_ker, killHom_X, ite_eq_right hnkilled]
    exact hXne
  exact hnot hmem

#print axioms xSegIdeal_lt_succ

/-- Height lower bound: the segment chain gives
`height(xSegIdeal k) ≥ k`. -/
theorem le_height_xSegIdeal (n : ℕ) (K : Type*) [Field K] (k : ℕ)
    (hk : k ≤ statementIndex n + 1) :
    ((k : ℕ) : ℕ∞) ≤ (xSegIdeal n K k).height := by
  revert hk
  induction k with
  | zero =>
      intro _hk0
      exact zero_le
  | succ k ih =>
      intro hk
      have hk' : k < statementIndex n + 1 := Nat.lt_of_succ_le hk
      have hlt := xSegIdeal_lt_succ n K k hk'
      have hstep := @Ideal.height_add_one_le_of_lt_of_isPrime _ _ _ _
        (xSegIdeal_isPrime n K k) (xSegIdeal_isPrime n K (k + 1)) hlt
      have ih' : ((k : ℕ) : ℕ∞) ≤ (xSegIdeal n K k).height :=
        ih (le_trans (Nat.le_succ k) hk)
      have hcast : (((k + 1 : ℕ)) : ℕ∞) = ((k : ℕ) : ℕ∞) + 1 := by norm_cast
      rw [hcast]
      exact le_trans (add_le_add_left ih' 1) hstep

#print axioms le_height_xSegIdeal

/-- A2(iii) `x`-ideal exclusion: the full `x`-ideal
(`xSegIdeal n K n`, span of all `x`-variables) is not a minimal prime
over any stage ideal — its height is `≥ n` (segment chain) against the
banked A2(i) cap `≤ j.val < n`. Pure height arithmetic: no `hN`, no
`horth`. -/
theorem xIdeal_notMem_minimalPrimes_stageIdeal (n : ℕ) (K : Type*) [Field K]
    (c : Fin n → Fin n → Fin n → K) (hn : 0 < n)
    (j : Fin (statementIndex n + 1)) :
    xSegIdeal n K n ∉ (MinAvoidRungs.stageIdeal n K c hn j).minimalPrimes := by
  intro hmem
  have hcap := AvoidanceCoreDimGe3.height_le_of_mem_minimalPrimes_stageIdeal
    n K c hn j _ hmem
  have hshift := shift_add_one n hn
  have hlow : ((n : ℕ) : ℕ∞) ≤ (xSegIdeal n K n).height :=
    le_height_xSegIdeal n K n (by omega)
  have hle : ((n : ℕ) : ℕ∞) ≤ ((j.val : ℕ) : ℕ∞) := le_trans hlow hcap
  have hnm : n ≤ j.val := by exact_mod_cast hle
  have hjlt := j.isLt
  omega

#print axioms xIdeal_notMem_minimalPrimes_stageIdeal

end A3aCloserDimKit
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
