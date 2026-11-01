/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointFromBezout
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoidRungs
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.AvoidanceCoreDimGe3
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.MinAvoid.A3aCloserDimKit
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.HeightCut.AdditivityClose
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.HeightCut.ConeCutAvoidance
import Section_2_Preliminaries.A_Preliminaries

/-!
# M-O1c: horth-free A3b-middle refactor

Verbatim copy of
`zNotMemAvoid_middle_of_cuts`
(merged here from `Hge2MinAvoidA3bMiddleClose.lean`) minus the `_horth` binder
, with the proof body (`:89-191`) copied unchanged. It elaborates
iff `horth` is truly unused — verified by full-proof reads plus an
indirect-use audit (design note §0, review §M-O1c): no `horth` mentions in
the body, and every called lemma (`hN_contra_of_cone_point`,
`lastRung_mem_all_of_mem`, `exists_ne_zero_mem_zeroLocus_of_height_le`,
`cutIdeal_ne_top_of_mem_minimalPrimes`,
`height_le_of_mem_minimalPrimes_stageIdeal`, `card_filter_gt`,
`bridgeSystem_homogeneous`) takes no `horth`. The elaboration check
(copy-paste body, drop binder) is the verification.

No separate last-rung refactor: the middle-close takes general `j` with
only `_hj : 2 ≤ j.val` (general `n`, no `hjlast`), so it covers the last
rung; the existing files are untouched. Plus a ~5-line ∀-form wrapper
producing exactly the `hA3b` input shape M-O1b/E10 (`:143-145`) take.

`[IsAlgClosed K]` is used inside the copied body via D4c
(`exists_ne_zero_mem_zeroLocus_of_height_le`, nonzero point from the
height bound) and the R4 PIT-cut bound
(`height_le_of_mem_minimalPrimes_cut_unconditional`, via closed
`heightCutAdditivity`). Documented here as `[algClosed]`; no other
classical or choice-like axiom is introduced (see `#print axioms`
below).

Status: A3b closer unconditional given algebra data + `[IsAlgClosed K]`,
no `horth`; Leg 2a A3b-half closed. Fires M-O1b's `hA3b` input.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace A3bMiddleRefactor

open scoped BigOperators

/-- General-`n` middle-rung A3b closer (all rungs), without `horth`:
every minimal prime over the stage ideal avoids the rung element, proved
by the multi-cut PIT argument (see the module docstring). The `z ∉ Q`
hypothesis and `_hj`/`_hnp` are carried for address compatibility and
unused — the leaf proves the stronger `z`-free statement and subsumes A3a.

`[IsAlgClosed K]`. -/
theorem zNotMemAvoid_middle_of_cuts_unhorth
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    [IsScalarTower K E E] [SMulCommClass K E E]
    (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0})
    (j : Fin (statementIndex n + 1)) (_hj : 2 ≤ j.val)
    (_hnp : ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime) :
    AvoidanceCoreDimGe3.ZNotMemAvoidCloser n K c hn j := by
  classical
  intro Q hQmin _hz
  by_contra hcon
  have hQQ : (bridgeSystem n K c hn) j ∈ Q := by simpa using hcon
  set cuts : Finset (MvPolynomial (Fin (statementIndex n + 2)) K) :=
    insert (AvoidanceCoreDimGe3.zVarPoly n K *
      AvoidanceCoreDimGe3.zVarPoly n K)
      (Finset.image (bridgeSystem n K c hn)
        (Finset.filter (fun k : Fin (statementIndex n + 1) => j.val < k.val)
          Finset.univ)) with hcuts
  have hcuts_hom : ∀ g ∈ cuts, g.IsHomogeneous 2 := by
    intro g hg
    rw [hcuts, Finset.mem_insert, Finset.mem_image] at hg
    rcases hg with rfl | ⟨k, _hk, rfl⟩
    · exact (MvPolynomial.isHomogeneous_X _ _).mul
        (MvPolynomial.isHomogeneous_X _ _)
    · exact bridgeSystem_homogeneous n K c hn k
  have hflt : (Finset.filter (fun k : Fin (statementIndex n + 1) => j.val < k.val)
        Finset.univ).card
      ≤ (statementIndex n + 1) - (j.val + 1) :=
    A3aCloserDimKit.card_filter_gt _ _ j.isLt
  have hcard : cuts.card ≤ 1 + ((statementIndex n + 1) - (j.val + 1)) := by
    have h1 : cuts.card ≤ (Finset.image (bridgeSystem n K c hn)
        (Finset.filter (fun k : Fin (statementIndex n + 1) => j.val < k.val)
          Finset.univ)).card + 1 := by
      rw [hcuts]
      exact Finset.card_insert_le _ _
    have h2 : (Finset.image (bridgeSystem n K c hn)
        (Finset.filter (fun k : Fin (statementIndex n + 1) => j.val < k.val)
          Finset.univ)).card ≤ (statementIndex n + 1) - (j.val + 1) :=
      le_trans Finset.card_image_le hflt
    omega
  have hproper :=
    A3aCloserDimKit.cutIdeal_ne_top_of_mem_minimalPrimes
      n K c hn j Q hQmin cuts hcuts_hom
  obtain ⟨P', hP'⟩ := Ideal.nonempty_minimalPrimes hproper
  have hQprime : Q.IsPrime := hQmin.isPrime
  have hP'prime : P'.IsPrime := hP'.isPrime
  have hP3 := @AdditivityClose.height_le_of_mem_minimalPrimes_cut_unconditional
    (statementIndex n) K _ _ Q P' hQprime hP'prime cuts hP'
  have hcap :=
    AvoidanceCoreDimGe3.height_le_of_mem_minimalPrimes_stageIdeal
      n K c hn j Q hQmin
  have h3 : P'.height ≤ (((statementIndex n + 1 : ℕ)) : ℕ∞) := by
    refine le_trans hP3 ?_
    have hmono : Q.height + ((cuts.card : ℕ) : ℕ∞)
        ≤ ((j.val : ℕ) : ℕ∞)
          + (((1 + ((statementIndex n + 1) - (j.val + 1)) : ℕ)) : ℕ∞) :=
      add_le_add hcap (by exact_mod_cast hcard)
    refine le_trans hmono ?_
    have harith : j.val + (1 + ((statementIndex n + 1) - (j.val + 1)))
        ≤ statementIndex n + 1 := by
      have hjlt := j.isLt
      omega
    have hcast : ((j.val : ℕ) : ℕ∞)
        + (((1 + ((statementIndex n + 1) - (j.val + 1)) : ℕ)) : ℕ∞)
        = ((((j.val + (1 + ((statementIndex n + 1) - (j.val + 1)))) : ℕ)) : ℕ∞) :=
      (Nat.cast_add _ _).symm
    rw [hcast]
    exact_mod_cast harith
  obtain ⟨a, haV, hane⟩ :=
    @A3aCloserDimKit.exists_ne_zero_mem_zeroLocus_of_height_le
      (statementIndex n) K _ _ P' hP'prime h3
  have hleQP : Q ≤ P' := le_trans le_sup_left hP'.le
  have ha0 : ∀ p ∈ P', MvPolynomial.aeval a p = 0 :=
    MvPolynomial.mem_zeroLocus_iff.mp haV
  have hzz : a (Fin.last (statementIndex n + 1)) = 0 := by
    have hmem : AvoidanceCoreDimGe3.zVarPoly n K *
        AvoidanceCoreDimGe3.zVarPoly n K ∈ P' := by
      apply hP'.le
      apply Ideal.mem_sup_right
      apply Ideal.subset_span
      rw [hcuts, Finset.mem_coe, Finset.mem_insert]
      exact Or.inl rfl
    have hev := ha0 _ hmem
    rw [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_mul] at hev
    simp only [AvoidanceCoreDimGe3.zVarPoly, MvPolynomial.eval_X] at hev
    exact mul_self_eq_zero.mp hev
  have hGall : ∀ k : Fin (statementIndex n + 1),
      MvPolynomial.eval a ((bridgeSystem n K c hn) k) = 0 := by
    intro k
    have hmem : (bridgeSystem n K c hn) k ∈ P' := by
      by_cases hk : k.val < j.val
      · apply hleQP
        apply hQmin.le
        exact Ideal.subset_span ⟨k, hk, rfl⟩
      · by_cases hkj : k.val = j.val
        · apply hleQP
          have hkj' : k = j := Fin.ext hkj
          rw [hkj']
          exact hQQ
        · apply hP'.le
          apply Ideal.mem_sup_right
          apply Ideal.subset_span
          rw [hcuts, Finset.mem_coe, Finset.mem_insert, Finset.mem_image]
          refine Or.inr ⟨k, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
    have hev := ha0 _ hmem
    rw [MvPolynomial.aeval_eq_eval] at hev
    exact hev
  exact ConeCutAvoidance.hN_contra_of_cone_point n K E V c b hexp hN hn a hane
    hzz hGall

#print axioms zNotMemAvoid_middle_of_cuts_unhorth

/-- ∀-form A3b closer, unconditional: exactly the `hA3b` input shape
M-O1b/E10 (`AvoidanceCoreDimGe3.lean`) take. Covers all rungs at
general `n` (no separate last-rung refactor).
-/
theorem zNotMemAvoidCloser_unhorth_forall
    (K E : Type*) [Field K] [IsAlgClosed K]
    [NonUnitalNonAssocSemiring E] [Module K E]
    [IsScalarTower K E E] [SMulCommClass K E E]
    (n : ℕ) (hn : 0 < n)
    (c : Fin n → Fin n → Fin n → K)
    (V : Submodule K E) (b : Module.Basis (Fin n) K V)
    (hexp : ∀ i j, (b i : E) * (b j : E)
      = ∑ k, c i j k • (b k : E))
    (hN : absNilpotent K E V = {0}) :
    ∀ j : Fin (statementIndex n + 1), 2 ≤ j.val →
      ¬ (MinAvoidRungs.stageIdeal n K c hn j).IsPrime →
      AvoidanceCoreDimGe3.ZNotMemAvoidCloser n K c hn j :=
  fun j hj hnp => zNotMemAvoid_middle_of_cuts_unhorth
    K E n hn c V b hexp hN j hj hnp

#print axioms zNotMemAvoidCloser_unhorth_forall

end A3bMiddleRefactor
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
