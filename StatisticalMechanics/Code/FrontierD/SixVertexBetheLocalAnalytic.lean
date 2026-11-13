/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheAnalyticContinuation
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Algebra.Module.LocallyConvex











open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section




theorem analyticAt_real_arctan (x : Real) :
    AnalyticAt Real Real.arctan x := by
  let a := Real.arctan x
  have hcos : Real.cos a ≠ 0 := (Real.cos_arctan_pos x).ne'
  have htan : AnalyticAt Real Real.tan a := by
    rw [show Real.tan = fun z => Real.sin z / Real.cos z by
      funext z
      rw [Real.tan_eq_sin_div_cos]]
    exact Real.analyticAt_sin.div Real.analyticAt_cos hcos
  let d : Real := 1 / Real.cos a ^ 2
  have hd : d ≠ 0 := by
    dsimp [d]
    positivity
  let i : Real ≃L[Real] Real :=
    ContinuousLinearEquiv.unitsEquivAut Real (.mk0 d hd)
  have hfderiv : fderiv Real Real.tan a = (i : Real →L[Real] Real) := by
    apply ContinuousLinearMap.ext
    intro y
    rw [(Real.hasDerivAt_tan hcos).hasFDerivAt.fderiv]
    simp [i, d, ContinuousLinearEquiv.unitsEquivAut_apply]
  dsimp [a] at htan hfderiv ⊢
  apply Real.tanPartialHomeomorph.analyticAt_symm
  · exact Set.mem_univ x
  · exact htan
  · exact hfderiv



theorem analyticAt_sixVertexTheta_joint
    (q : Real × (Real × Real)) (hc : 2 < q.1) :
    AnalyticAt Real
      (fun z : Real × (Real × Real) =>
        sixVertexTheta z.1 z.2.1 z.2.2) q := by
  unfold sixVertexTheta sixVertexThetaDenominator sixVertexDelta
  have hden : Real.cos q.2.1 + Real.cos q.2.2 -
      2 * ((2 - q.1 ^ 2) / 2) ≠ 0 := by
    have hx := Real.neg_one_le_cos q.2.1
    have hy := Real.neg_one_le_cos q.2.2
    nlinarith
  have hcA : AnalyticAt Real
      (fun z : Real × (Real × Real) => z.1) q :=
    (ContinuousLinearMap.fst Real Real (Real × Real)).analyticAt q
  have hxA : AnalyticAt Real
      (fun z : Real × (Real × Real) => z.2.1) q :=
    ((ContinuousLinearMap.fst Real Real Real).comp
      (ContinuousLinearMap.snd Real Real (Real × Real))).analyticAt q
  have hyA : AnalyticAt Real
      (fun z : Real × (Real × Real) => z.2.2) q :=
    ((ContinuousLinearMap.snd Real Real Real).comp
      (ContinuousLinearMap.snd Real Real (Real × Real))).analyticAt q
  have hnum : AnalyticAt Real
      (fun z : Real × (Real × Real) =>
        Real.sin z.2.1 - Real.sin z.2.2) q :=
    (Real.analyticAt_sin.comp hxA).sub (Real.analyticAt_sin.comp hyA)
  have hdeltaA : AnalyticAt Real
      (fun z : Real × (Real × Real) => (2 - z.1 ^ 2) / 2) q :=
    (analyticAt_const.sub (hcA.pow 2)).div_const
  have hdenA : AnalyticAt Real
      (fun z : Real × (Real × Real) =>
        Real.cos z.2.1 + Real.cos z.2.2 -
          2 * ((2 - z.1 ^ 2) / 2)) q :=
    ((Real.analyticAt_cos.comp hxA).add
      (Real.analyticAt_cos.comp hyA)).sub
        (analyticAt_const.mul hdeltaA)
  have hratio := hnum.div hdenA hden
  have harctan : AnalyticAt Real
      (fun z : Real × (Real × Real) =>
        Real.arctan ((Real.sin z.2.1 - Real.sin z.2.2) /
          (Real.cos z.2.1 + Real.cos z.2.2 -
            2 * ((2 - z.1 ^ 2) / 2)))) q :=
    (analyticAt_real_arctan _).comp hratio
  exact (hyA.sub hxA).add (analyticAt_const.mul harctan)



theorem analyticAt_sixVertexBetheResidual_family
    (N n : Nat) (q : Real × (Fin n → Real)) (hc : 2 < q.1) :
    AnalyticAt Real
      (fun z : Real × (Fin n → Real) =>
        fun j => sixVertexBetheResidual z.1 N n z.2 j) q := by
  apply AnalyticAt.pi
  intro j
  let sndP : (Real × (Fin n → Real)) →L[Real] (Fin n → Real) :=
    ContinuousLinearMap.snd Real Real (Fin n → Real)
  have hcA : AnalyticAt Real
      (fun z : Real × (Fin n → Real) => z.1) q :=
    (ContinuousLinearMap.fst Real Real (Fin n → Real)).analyticAt q
  have hjA : AnalyticAt Real
      (fun z : Real × (Fin n → Real) => z.2 j) q :=
    ((ContinuousLinearMap.proj j).comp sndP).analyticAt q
  have htheta (k : Fin n) : AnalyticAt Real
      (fun z : Real × (Fin n → Real) =>
        sixVertexTheta z.1 (z.2 j) (z.2 k)) q := by
    have hkA : AnalyticAt Real
        (fun z : Real × (Fin n → Real) => z.2 k) q :=
      ((ContinuousLinearMap.proj k).comp sndP).analyticAt q
    have hmap : AnalyticAt Real
        (fun z : Real × (Fin n → Real) =>
          (z.1, (z.2 j, z.2 k))) q := hcA.prod (hjA.prod hkA)
    exact (analyticAt_sixVertexTheta_joint
      (q.1, (q.2 j, q.2 k)) hc).comp
        (f := fun z : Real × (Fin n → Real) =>
          (z.1, (z.2 j, z.2 k))) (x := q) hmap
  have hsum : AnalyticAt Real
      (fun z : Real × (Fin n → Real) =>
        ∑ k, sixVertexTheta z.1 (z.2 j) (z.2 k)) q :=
    Finset.analyticAt_fun_sum Finset.univ (fun k _ => htheta k)
  unfold sixVertexBetheResidual
  exact ((analyticAt_const.mul hjA).add hsum).sub analyticAt_const



def sixVertexBetheResidualGraph (N n : Nat) :
    (Real × (Fin n → Real)) → (Real × (Fin n → Real)) :=
  fun q => (q.1, fun j => sixVertexBetheResidual q.1 N n q.2 j)

theorem analyticAt_sixVertexBetheResidualGraph
    (N n : Nat) (q : Real × (Fin n → Real)) (hc : 2 < q.1) :
    AnalyticAt Real (sixVertexBetheResidualGraph N n) q := by
  exact analyticAt_fst.prod
    (analyticAt_sixVertexBetheResidual_family N n q hc)




def sixVertexBetheRootJacobian (N n : Nat) (c : Real)
    (p : Fin n → Real) :
    (Fin n → Real) →L[Real] (Fin n → Real) :=
  fderiv Real (fun q : Fin n → Real =>
    fun j => sixVertexBetheResidual c N n q j) p




theorem sixVertexBetheResidualGraph_fderiv_injective_of_rootJacobian
    {N n : Nat} {c : Real} (hc : 2 < c) {p : Fin n → Real}
    (hjac : Function.Injective (sixVertexBetheRootJacobian N n c p)) :
    Function.Injective
      (fderiv Real (sixVertexBetheResidualGraph N n) (c, p)) := by
  let H := sixVertexBetheResidualGraph N n
  let L := fderiv Real H (c, p)
  let J := sixVertexBetheRootJacobian N n c p
  have hH : HasFDerivAt H L (c, p) :=
    (analyticAt_sixVertexBetheResidualGraph N n (c, p) hc).hasStrictFDerivAt.hasFDerivAt
  let incl : (Fin n → Real) →L[Real]
      (Real × (Fin n → Real)) :=
    (0 : (Fin n → Real) →L[Real] Real).prod
      (ContinuousLinearMap.id Real (Fin n → Real))
  have hincl : HasFDerivAt (fun q : Fin n → Real => (c, q)) incl p :=
    (hasFDerivAt_const c p).prodMk (hasFDerivAt_id p)
  have hcomp : HasFDerivAt
      (fun q : Fin n → Real => H (c, q)) (L.comp incl) p :=
    hH.comp p hincl
  have hres : HasFDerivAt
      (fun q : Fin n → Real =>
        fun j => sixVertexBetheResidual c N n q j) J p := by
    exact (analyticAt_sixVertexBetheResidual_family N n (c, p) hc).comp
      (x := p) (f := fun q : Fin n → Real => (c, q))
      (analyticAt_const.prod analyticAt_id) |>.hasStrictFDerivAt.hasFDerivAt
  let direct : (Fin n → Real) →L[Real]
      (Real × (Fin n → Real)) :=
    (0 : (Fin n → Real) →L[Real] Real).prod J
  have hdirect : HasFDerivAt
      (fun q : Fin n → Real => H (c, q)) direct p := by
    exact (hasFDerivAt_const c p).prodMk hres
  have hderiv : L.comp incl = direct := hcomp.unique hdirect
  intro z w hzw
  let u := z - w
  have hu : L u = 0 := by
    dsimp [u, L]
    rw [map_sub, hzw, sub_self]
  have hfst : u.1 = 0 := by
    have hproj : HasFDerivAt (fun q : Real × (Fin n → Real) => q.1)
        (ContinuousLinearMap.fst Real Real (Fin n → Real)) (c, p) :=
      (ContinuousLinearMap.fst Real Real (Fin n → Real)).hasFDerivAt
    have hcompFst : HasFDerivAt
        (fun q : Real × (Fin n → Real) => q.1)
        ((ContinuousLinearMap.fst Real Real (Fin n → Real)).comp L)
        (c, p) := by
      simpa [H, sixVertexBetheResidualGraph] using
        ((ContinuousLinearMap.fst Real Real (Fin n → Real)).hasFDerivAt.comp
          (c, p) hH)
    have hfstL :
        (ContinuousLinearMap.fst Real Real (Fin n → Real)).comp L =
          ContinuousLinearMap.fst Real Real (Fin n → Real) :=
      hcompFst.unique hproj
    have h := congrArg
      (fun T : (Real × (Fin n → Real)) →L[Real] Real => T u) hfstL
    simpa [hu] using h.symm
  have hupair : u = (0, u.2) := Prod.ext hfst rfl
  have hJzero : J u.2 = 0 := by
    have happly := congrArg
      (fun T : (Fin n → Real) →L[Real]
        (Real × (Fin n → Real)) => T u.2) hderiv
    have hLzero : L (incl u.2) = 0 := by
      rw [show incl u.2 = u by
        rw [hupair]
        rfl]
      exact hu
    simpa [hLzero, direct] using (congrArg Prod.snd happly).symm
  have hu2 : u.2 = 0 := hjac (by simpa using hJzero)
  have hsub : z - w = 0 := by
    change u = 0
    exact Prod.ext hfst hu2
  exact sub_eq_zero.mp hsub


theorem isOpen_sixVertexStrictRootTuples (n : Nat) :
    IsOpen {p : Fin n → Real | StrictMono p} := by
  rw [show {p : Fin n → Real | StrictMono p} =
      ⋂ i, ⋂ j, ⋂ (_h : i < j), {p | p i < p j} by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact Iff.rfl]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ =>
      isOpen_lt (continuous_apply i) (continuous_apply j)



theorem isOpen_sixVertexRootsInOpenInterval (n : Nat) :
    IsOpen {p : Fin n → Real | SixVertexRootsInOpenInterval p} := by
  rw [show {p : Fin n → Real | SixVertexRootsInOpenInterval p} =
      ⋂ j, {p | -Real.pi < p j ∧ p j < Real.pi} by
    ext p
    simp [SixVertexRootsInOpenInterval]]
  exact isOpen_iInter_of_finite fun j =>
    (isOpen_lt continuous_const (continuous_apply j)).inter
      (isOpen_lt (continuous_apply j) continuous_const)



theorem isOpen_sixVertexNonsymmetricOpenRootDomain (n : Nat) :
    IsOpen {p : Fin n → Real |
      StrictMono p ∧ SixVertexRootsInOpenInterval p} :=
  (isOpen_sixVertexStrictRootTuples n).inter
    (isOpen_sixVertexRootsInOpenInterval n)



def sixVertexBetheFixedPointSet (c : Real) (N n : Nat) :
    Set (Fin n → Real) :=
  {p | SixVertexClosedRootSimplex p ∧ sixVertexBetheUpdate c N n p = p}

theorem isCompact_sixVertexBetheFixedPointSet
    {c : Real} (hc : 2 < c) (N n : Nat) :
    IsCompact (sixVertexBetheFixedPointSet c N n) := by
  have hclosed : IsClosed {p : Fin n → Real |
      sixVertexBetheUpdate c N n p = p} :=
    isClosed_eq (continuous_sixVertexBetheUpdate hc N n) continuous_id
  exact (isCompact_sixVertexClosedRootSimplex n).inter_right hclosed

theorem sixVertexBetheFixedPointSet_nonempty
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N) :
    (sixVertexBetheFixedPointSet c N n).Nonempty := by
  obtain ⟨p, hp, hfix⟩ :=
    exists_sixVertexBetheUpdate_fixedPoint hc hN hhalf
  exact ⟨p, hp, hfix⟩


theorem sixVertexBetheFixedPointSet_subset_open
    {c : Real} (hc : 2 < c) {N n : Nat} (hhalf : 2 * n ≤ N) :
    sixVertexBetheFixedPointSet c N n ⊆
      {p | SixVertexOpenRootSimplex p} := by
  rintro p ⟨hp, hfix⟩
  exact sixVertexBetheUpdate_fixedPoint_mem_open hc hhalf hp hfix

theorem sixVertexBetheFixedPointSet_eq_solutionSet
    {c : Real} {N n : Nat} (hN : 0 < N) :
    sixVertexBetheFixedPointSet c N n =
      {p | SixVertexClosedRootSimplex p ∧
        SixVertexSatisfiesBetheEquations c N n p} := by
  ext p
  simp only [sixVertexBetheFixedPointSet, Set.mem_setOf_eq]
  rw [sixVertexBetheUpdate_eq_self_iff hN p]

theorem continuous_sixVertexBetheResidual_family_clamp
    {a : Real} (ha : 2 < a) (N n : Nat) :
    Continuous (fun q : Real × (Fin n → Real) =>
      fun j => sixVertexBetheResidual (max a q.1) N n q.2 j) := by
  rw [continuous_iff_continuousAt]
  intro q
  have hc : 2 < max a q.1 := ha.trans_le (le_max_left _ _)
  have hbase := (analyticAt_sixVertexBetheResidual_family N n
    (max a q.1, q.2) hc).continuousAt
  have hmap : ContinuousAt
      (fun z : Real × (Fin n → Real) => (max a z.1, z.2)) q := by
    fun_prop
  exact hbase.comp
    (f := fun z : Real × (Fin n → Real) => (max a z.1, z.2))
    (x := q) hmap

theorem continuous_sixVertexBetheUpdate_family_clamp
    {a : Real} (ha : 2 < a) {N n : Nat} (hN : 0 < N) :
    Continuous (fun q : Real × (Fin n → Real) =>
      sixVertexBetheUpdate (max a q.1) N n q.2) := by
  have hres := continuous_sixVertexBetheResidual_family_clamp ha N n
  have heq : (fun q : Real × (Fin n → Real) =>
      sixVertexBetheUpdate (max a q.1) N n q.2) =
      fun q => q.2 - (1 / (N : Real)) •
        (fun j => sixVertexBetheResidual (max a q.1) N n q.2 j) := by
    funext q j
    have h := sixVertexBetheResidual_eq_updateSub hN q.2 j
      (c := max a q.1)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    change _ = q.2 j - (1 / (N : Real)) * _
    change sixVertexBetheResidual (max a q.1) N n q.2 j = _ at h
    have hNr : (0 : Real) < N := by exact_mod_cast hN
    rw [h]
    field_simp [hNr.ne']
    ring
  rw [heq]
  exact continuous_snd.sub (continuous_const.smul hres)


def sixVertexBetheContinuationSet
    (a b : Real) (N n : Nat) : Set (Real × (Fin n → Real)) :=
  {q | q.1 ∈ Set.Icc a b ∧ SixVertexClosedRootSimplex q.2 ∧
    sixVertexBetheUpdate q.1 N n q.2 = q.2}

theorem isCompact_sixVertexBetheContinuationSet
    {a b : Real} (ha : 2 < a) {N n : Nat} (hN : 0 < N) :
    IsCompact (sixVertexBetheContinuationSet a b N n) := by
  let S : Set (Fin n → Real) := {p | SixVertexClosedRootSimplex p}
  have hbase : IsCompact (Set.Icc a b ×ˢ S) :=
    isCompact_Icc.prod (isCompact_sixVertexClosedRootSimplex n)
  have hU := continuous_sixVertexBetheUpdate_family_clamp
    (n := n) ha hN
  have heqclosed : IsClosed {q : Real × (Fin n → Real) |
      sixVertexBetheUpdate (max a q.1) N n q.2 = q.2} :=
    isClosed_eq hU continuous_snd
  rw [show sixVertexBetheContinuationSet a b N n =
      (Set.Icc a b ×ˢ S) ∩
        {q | sixVertexBetheUpdate (max a q.1) N n q.2 = q.2} by
    ext q
    simp only [sixVertexBetheContinuationSet, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc]
    constructor
    · rintro ⟨hab, hp, hfix⟩
      exact ⟨⟨hab, hp⟩,
        by simpa [max_eq_right hab.1] using hfix⟩
    · rintro ⟨⟨hab, hp⟩, hfix⟩
      exact ⟨hab, hp,
        by simpa [max_eq_right hab.1] using hfix⟩]
  exact hbase.inter_right heqclosed

theorem sixVertexBetheContinuationSet_fiber_nonempty
    {a b t : Real} (ha : 2 < a) (ht : t ∈ Set.Icc a b)
    {N n : Nat} (hN : 0 < N) (hhalf : 2 * n ≤ N) :
    ∃ p, (t, p) ∈ sixVertexBetheContinuationSet a b N n := by
  have htc : 2 < t := ha.trans_le ht.1
  obtain ⟨p, hp, hfix⟩ :=
    exists_sixVertexBetheUpdate_fixedPoint htc hN hhalf
  exact ⟨p, ht, hp, hfix⟩

theorem sixVertexBetheContinuationSet_fst_image
    {a b : Real} (ha : 2 < a) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N) :
    Prod.fst '' sixVertexBetheContinuationSet a b N n = Set.Icc a b := by
  ext t
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq.1
  · intro ht
    obtain ⟨p, hp⟩ := sixVertexBetheContinuationSet_fiber_nonempty
      ha ht hN hhalf
    exact ⟨(t, p), hp, rfl⟩



theorem sixVertexBetheContinuationSet_subset_open
    {a b : Real} (ha : 2 < a) {N n : Nat} (hhalf : 2 * n ≤ N) :
    sixVertexBetheContinuationSet a b N n ⊆
      {q | SixVertexOpenRootSimplex q.2} := by
  rintro q ⟨hqIcc, hqclosed, hqfix⟩
  exact sixVertexBetheUpdate_fixedPoint_mem_open
    (ha.trans_le hqIcc.1) hhalf hqclosed hqfix


abbrev SixVertexBetheContinuationSpace
    (a b : Real) (N n : Nat) :=
  sixVertexBetheContinuationSet a b N n


def sixVertexBetheContinuationProjection
    {a b : Real} {N n : Nat} :
    SixVertexBetheContinuationSpace a b N n → Set.Icc a b :=
  fun q => ⟨q.1.1, q.2.1⟩

theorem continuous_sixVertexBetheContinuationProjection
    {a b : Real} {N n : Nat} :
    Continuous (@sixVertexBetheContinuationProjection a b N n) :=
  continuous_subtype_val.fst.subtype_mk _





theorem exists_sixVertexContinuousBetheBranch_of_isLocalHomeomorph
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N n : Nat} (hN : 0 < N)
    (hlocal : IsLocalHomeomorph
      (@sixVertexBetheContinuationProjection a b N n))
    (z₀ : SixVertexBetheContinuationSpace a b N n)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin n → Real),
      roots c₀ = z₀.1.2 ∧
      ∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N n (roots t) := by
  have hcompact := isCompact_sixVertexBetheContinuationSet
    (b := b) (n := n) ha hN
  letI : CompactSpace (SixVertexBetheContinuationSpace a b N n) :=
    isCompact_iff_compactSpace.mp hcompact
  have hproj : Continuous
      (@sixVertexBetheContinuationProjection a b N n) :=
    continuous_sixVertexBetheContinuationProjection
  have hcovOn : IsCoveringMapOn
      (@sixVertexBetheContinuationProjection a b N n) Set.univ :=
    IsCoveringMapOn.of_openPartialHomeomorph hproj
      (fun e _ => by
        obtain ⟨phi, he, hphi⟩ := hlocal e
        exact ⟨phi, he, hphi.symm⟩)
  have hcov : IsCoveringMap
      (@sixVertexBetheContinuationProjection a b N n) :=
    isCoveringMap_iff_isCoveringMapOn_univ.mpr hcovOn
  let clamp : Real → Set.Icc a b := fun t =>
    ⟨min b (max a t),
      ⟨le_min hab (le_max_left _ _), min_le_left _ _⟩⟩
  have hclamp : Continuous clamp :=
    Continuous.subtype_mk (by fun_prop) _
  let f : C(Real, Set.Icc a b) := ⟨clamp, hclamp⟩
  have hf₀ : f c₀ = sixVertexBetheContinuationProjection z₀ := by
    rw [hz₀]
    apply Subtype.ext
    simp [f, clamp, max_eq_right hc₀.1, min_eq_right hc₀.2]
  letI : ContractibleSpace Real :=
    (contractible_iff_id_nullhomotopic Real).mpr
      ⟨0, ⟨ContinuousMap.Homotopy.affine
        (ContinuousMap.id Real) (ContinuousMap.const Real 0)⟩⟩
  obtain ⟨F, hF₀, hFlift⟩ :=
    (hcov.existsUnique_continuousMap_lifts f c₀ z₀ hf₀.symm).exists
  let roots : C(Real, Fin n → Real) :=
    ⟨fun t => (F t).1.2,
      continuous_subtype_val.snd.comp F.continuous⟩
  refine ⟨roots, ?_, ?_⟩
  · change (F c₀).1.2 = z₀.1.2
    rw [hF₀]
  · intro t ht
    have hprojF := congrFun hFlift t
    have hclamp_t : f t = ⟨t, ht⟩ := by
      apply Subtype.ext
      simp [f, clamp, max_eq_right ht.1, min_eq_right ht.2]
    have hfirst : (F t).1.1 = t := by
      have h := congrArg Subtype.val hprojF
      simpa [hclamp_t, sixVertexBetheContinuationProjection] using h
    have hmem := (F t).2
    have hfix : sixVertexBetheUpdate t N n (F t).1.2 = (F t).1.2 := by
      calc
        sixVertexBetheUpdate t N n (F t).1.2 =
            sixVertexBetheUpdate (F t).1.1 N n (F t).1.2 := by
          exact congrArg
            (fun s => sixVertexBetheUpdate s N n (F t).1.2) hfirst.symm
        _ = (F t).1.2 := hmem.2.2
    exact (sixVertexBetheUpdate_eq_self_iff hN _).mp hfix




structure SixVertexLocalAnalyticBetheBranch
    (N n : Nat) (c : Real) (p : Fin n → Real) where
  roots : Real → (Fin n → Real)
  analyticAt_roots : AnalyticAt Real roots c
  roots_at : roots c = p
  eventually_solution : ∀ᶠ t in 𝓝 c,
    SixVertexSatisfiesBetheEquations t N n (roots t)
  eventually_unique : ∀ᶠ q : Real × (Fin n → Real) in 𝓝 (c, p),
    SixVertexSatisfiesBetheEquations q.1 N n q.2 → roots q.1 = q.2




theorem exists_sixVertexLocalAnalyticBetheBranch
    {N n : Nat} {c : Real} (hc : 2 < c) {p : Fin n → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N n p)
    (hjac : Function.Injective
      (fderiv Real (sixVertexBetheResidualGraph N n) (c, p))) :
    Nonempty (SixVertexLocalAnalyticBetheBranch N n c p) := by
  let q₀ : Real × (Fin n → Real) := (c, p)
  let H := sixVertexBetheResidualGraph N n
  let L := fderiv Real H q₀
  have hH : AnalyticAt Real H q₀ :=
    analyticAt_sixVertexBetheResidualGraph N n q₀ hc
  have hker : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hjac
  have hrange : L.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    exact LinearMap.injective_iff_surjective.mp hjac
  let e : (Real × (Fin n → Real)) ≃L[Real]
      (Real × (Fin n → Real)) :=
    ContinuousLinearEquiv.ofBijective L hker hrange
  have hHe : HasStrictFDerivAt H
      (e : (Real × (Fin n → Real)) →L[Real]
        (Real × (Fin n → Real))) q₀ := by
    simpa [L, e, ContinuousLinearEquiv.coe_ofBijective] using
      hH.hasStrictFDerivAt
  let R : OpenPartialHomeomorph
      (Real × (Fin n → Real)) (Real × (Fin n → Real)) :=
    hHe.toOpenPartialHomeomorph H
  have hqsource : q₀ ∈ R.source := hHe.mem_toOpenPartialHomeomorph_source
  have hzero : (fun j => sixVertexBetheResidual c N n p j) = 0 := by
    funext j
    exact (sixVertexBetheResidual_eq_zero_iff c N n p).2 hsol j
  have hHq₀ : H q₀ = (c, (0 : Fin n → Real)) := by
    apply Prod.ext
    · rfl
    · simpa [H, q₀, sixVertexBetheResidualGraph] using hzero
  have hR : AnalyticAt Real R.symm (H q₀) := by
    apply R.analyticAt_symm' hqsource
    · simpa [R] using hH
    · simpa [R] using hHe.hasFDerivAt.fderiv
  let roots : Real → (Fin n → Real) :=
    fun t => (R.symm (t, (0 : Fin n → Real))).2
  have hroots : AnalyticAt Real roots c := by
    rw [hHq₀] at hR
    have hinput : AnalyticAt Real
        (fun t : Real => (t, (0 : Fin n → Real))) c :=
      analyticAt_id.prod analyticAt_const
    have hcomp : AnalyticAt Real
        (R.symm ∘ fun t : Real => (t, (0 : Fin n → Real))) c :=
      hR.comp (f := fun t : Real => (t, (0 : Fin n → Real)))
        (x := c) hinput
    have hsnd : AnalyticAt Real
        (Prod.snd ∘ R.symm ∘
          fun t : Real => (t, (0 : Fin n → Real))) c :=
      analyticAt_snd.comp hcomp
    simpa only [Function.comp_apply] using hsnd
  have hrootsAt : roots c = p := by
    have hleft := R.left_inv hqsource
    have hinv : R.symm (c, (0 : Fin n → Real)) = (c, p) := by
      rw [← hHq₀]
      simpa [R, q₀] using hleft
    exact congrArg Prod.snd hinv
  have hright := hHe.eventually_right_inverse
  have hinput : Tendsto
      (fun t : Real => (t, (0 : Fin n → Real)))
      (𝓝 c) (𝓝 (H q₀)) := by
    rw [hHq₀]
    exact continuousAt_id.prodMk continuousAt_const
  have hbranchEq : ∀ᶠ t in 𝓝 c,
      H (R.symm (t, (0 : Fin n → Real))) =
        (t, (0 : Fin n → Real)) :=
    hinput.eventually hright
  have hsolution : ∀ᶠ t in 𝓝 c,
      SixVertexSatisfiesBetheEquations t N n (roots t) := by
    filter_upwards [hbranchEq] with t ht
    apply (sixVertexBetheResidual_eq_zero_iff t N n (roots t)).1
    intro j
    have hfst := congrArg Prod.fst ht
    have hsnd := congrArg Prod.snd ht
    change (R.symm (t, (0 : Fin n → Real))).1 = t at hfst
    change (fun j => sixVertexBetheResidual
      (R.symm (t, (0 : Fin n → Real))).1 N n
      (R.symm (t, (0 : Fin n → Real))).2 j) = 0 at hsnd
    rw [hfst] at hsnd
    exact congrFun (by simpa [roots] using hsnd) j
  have hsource : ∀ᶠ q : Real × (Fin n → Real) in 𝓝 q₀,
      q ∈ R.source := R.open_source.mem_nhds hqsource
  have hunique : ∀ᶠ q : Real × (Fin n → Real) in 𝓝 q₀,
      SixVertexSatisfiesBetheEquations q.1 N n q.2 → roots q.1 = q.2 := by
    filter_upwards [hsource] with q hq hqsol
    have hqzero : (fun j => sixVertexBetheResidual q.1 N n q.2 j) = 0 := by
      funext j
      exact (sixVertexBetheResidual_eq_zero_iff q.1 N n q.2).2 hqsol j
    have hHq : H q = (q.1, (0 : Fin n → Real)) := by
      apply Prod.ext
      · rfl
      · simpa [H, sixVertexBetheResidualGraph] using hqzero
    have hleft := R.left_inv hq
    have hinv : R.symm (q.1, (0 : Fin n → Real)) = q := by
      rw [← hHq]
      simpa [R] using hleft
    exact congrArg Prod.snd hinv
  exact ⟨{
    roots := roots
    analyticAt_roots := hroots
    roots_at := hrootsAt
    eventually_solution := hsolution
    eventually_unique := by simpa [q₀] using hunique
  }⟩



theorem exists_sixVertexLocalAnalyticBetheBranch_of_rootJacobian
    {N n : Nat} {c : Real} (hc : 2 < c) {p : Fin n → Real}
    (hsol : SixVertexSatisfiesBetheEquations c N n p)
    (hjac : Function.Injective (sixVertexBetheRootJacobian N n c p)) :
    Nonempty (SixVertexLocalAnalyticBetheBranch N n c p) :=
  exists_sixVertexLocalAnalyticBetheBranch hc hsol
    (sixVertexBetheResidualGraph_fderiv_injective_of_rootJacobian hc hjac)





theorem isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_rootJacobian
    {a b : Real} (ha : 2 < a) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N)
    (C : Set (SixVertexBetheContinuationSpace a b N n))
    (hjac : ∀ q ∈ C,
      Function.Injective (sixVertexBetheRootJacobian N n q.1.1 q.1.2)) :
    IsLocalHomeomorphOn
      (@sixVertexBetheContinuationProjection a b N n) C := by
  rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  intro z hzC
  let c : Real := z.1.1
  let p : Fin n → Real := z.1.2
  have hcIcc : c ∈ Set.Icc a b := z.2.1
  have hc : 2 < c := ha.trans_le hcIcc.1
  have hpclosed : SixVertexClosedRootSimplex p := z.2.2.1
  have hpfix : sixVertexBetheUpdate c N n p = p := z.2.2.2
  have hpsol : SixVertexSatisfiesBetheEquations c N n p :=
    (sixVertexBetheUpdate_eq_self_iff hN p).mp hpfix
  have hpopen : SixVertexOpenRootSimplex p :=
    sixVertexBetheUpdate_fixedPoint_mem_open hc hhalf hpclosed hpfix
  obtain ⟨B⟩ := exists_sixVertexLocalAnalyticBetheBranch_of_rootJacobian
    hc hpsol (hjac z hzC)
  obtain ⟨A, hA_sub, hA_open, hqA⟩ :=
    mem_nhds_iff.mp B.eventually_unique
  have hroot_cont : ContinuousAt B.roots c :=
    B.analyticAt_roots.continuousAt
  have hroot_tendsto : Tendsto B.roots (nhds c) (nhds p) := by
    rw [← congrArg nhds B.roots_at]
    exact hroot_cont
  have hgraph_tendsto : Tendsto (fun t => (t, B.roots t))
      (nhds c) (nhds (c, p)) := by
    have heq : (c, B.roots c) = (c, p) := Prod.ext rfl B.roots_at
    rw [← congrArg nhds heq]
    exact continuousAt_id.prodMk hroot_cont
  have hgraphA : ∀ᶠ t in nhds c, (t, B.roots t) ∈ A :=
    hgraph_tendsto.eventually (hA_open.mem_nhds hqA)
  have hrev_tendsto : Tendsto
      (fun t => (t, fun j : Fin n => -B.roots t j.rev))
      (nhds c) (nhds (c, p)) := by
    have hrevroot : ContinuousAt
        (fun t => fun j : Fin n => -B.roots t j.rev) c := by
      rw [continuousAt_pi]
      intro j
      exact ((continuous_apply j.rev).continuousAt.comp hroot_cont).neg
    have hcont := continuousAt_id.prodMk hrevroot
    have hrev_at : (fun j : Fin n => -B.roots c j.rev) = p := by
      rw [B.roots_at]
      exact hpopen.2.1.reverse_neg
    have heq : (c, fun j : Fin n => -B.roots c j.rev) = (c, p) :=
      Prod.ext rfl hrev_at
    rw [← congrArg nhds heq]
    exact hcont
  have hrev_unique : ∀ᶠ t in nhds c,
      SixVertexSatisfiesBetheEquations t N n
          (fun j : Fin n => -B.roots t j.rev) →
        B.roots t = (fun j : Fin n => -B.roots t j.rev) :=
    hrev_tendsto.eventually B.eventually_unique
  have hsymm : ∀ᶠ t in nhds c,
      SixVertexRootSymmetric (B.roots t) := by
    filter_upwards [B.eventually_solution, hrev_unique] with t ht htu
    have heq := htu ht.reverse_neg
    intro j
    have hj := congrFun heq j.rev
    simpa using hj
  let D : Set (Fin n → Real) :=
    {q | StrictMono q ∧ SixVertexRootsInOpenInterval q}
  have hD_open : IsOpen D :=
    isOpen_sixVertexNonsymmetricOpenRootDomain n
  have hpD : p ∈ D := ⟨hpopen.1, hpopen.2.2⟩
  have hrootD : ∀ᶠ t in nhds c, B.roots t ∈ D :=
    hroot_tendsto.eventually (hD_open.mem_nhds hpD)
  let Good : Real → Prop := fun t =>
    ContinuousAt B.roots t ∧
    SixVertexSatisfiesBetheEquations t N n (B.roots t) ∧
    B.roots t ∈ D ∧
    SixVertexRootSymmetric (B.roots t) ∧
    (t, B.roots t) ∈ A
  have hgood : ∀ᶠ t in nhds c, Good t := by
    filter_upwards [B.analyticAt_roots.eventually_continuousAt,
      B.eventually_solution, hrootD, hsymm, hgraphA] with t hct hsol hD hsy hA
    exact ⟨hct, hsol, hD, hsy, hA⟩
  obtain ⟨W, hW_sub, hW_open, hcW⟩ := mem_nhds_iff.mp hgood
  let V : Set (Set.Icc a b) := {t | (t.1 : Real) ∈ W}
  have hV_open : IsOpen V :=
    hW_open.preimage continuous_subtype_val
  let U : Set (SixVertexBetheContinuationSpace a b N n) :=
    {q | q.1 ∈ A ∧ q.1.1 ∈ W}
  have hU_open : IsOpen U :=
    (hA_open.preimage continuous_subtype_val).inter
      (hW_open.preimage continuous_subtype_val.fst)
  have hzU : z ∈ U := ⟨hqA, hcW⟩
  have hbranch_mem (t : V) :
      (t.1.1, B.roots t.1.1) ∈
        sixVertexBetheContinuationSet a b N n := by
    have htgood := hW_sub t.2
    have htopen : SixVertexOpenRootSimplex (B.roots t.1.1) :=
      ⟨htgood.2.2.1.1, htgood.2.2.2.1, htgood.2.2.1.2⟩
    exact ⟨t.1.2, htopen.toClosed,
      (sixVertexBetheUpdate_eq_self_iff hN _).mpr htgood.2.1⟩
  let e : U ≃ V :=
    { toFun := fun q =>
        ⟨sixVertexBetheContinuationProjection q.1, q.2.2⟩
      invFun := fun t =>
        ⟨⟨(t.1.1, B.roots t.1.1), hbranch_mem t⟩,
          (hW_sub t.2).2.2.2.2, t.2⟩
      left_inv := by
        intro q
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have hqsol : SixVertexSatisfiesBetheEquations
              q.1.1.1 N n q.1.1.2 :=
            (sixVertexBetheUpdate_eq_self_iff hN _).mp q.1.2.2.2
          exact hA_sub q.2.1 hqsol
      right_inv := by
        intro t
        apply Subtype.ext
        rfl }
  have he_cont : Continuous e :=
    Continuous.subtype_mk
      (continuous_sixVertexBetheContinuationProjection.comp
        continuous_subtype_val) _
  have he_inv_cont : Continuous e.symm := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hrootsV : Continuous (fun t : V => B.roots t.1.1) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact ((hW_sub t.2).1.comp_of_eq
        (continuous_subtype_val.comp continuous_subtype_val).continuousAt rfl)
    exact (continuous_subtype_val.comp continuous_subtype_val).prodMk hrootsV
  let E : U ≃ₜ V := Homeomorph.mk e he_cont he_inv_cont
  refine ⟨U, hU_open.mem_nhds hzU, ?_⟩
  have hemb := hV_open.isOpenEmbedding_subtypeVal.comp E.isOpenEmbedding
  simpa [E, e, U, V, sixVertexBetheContinuationProjection,
    Function.comp_def] using hemb




theorem isLocalHomeomorph_sixVertexBetheContinuationProjection_of_rootJacobian
    {a b : Real} (ha : 2 < a) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N)
    (hjac : ∀ q ∈ sixVertexBetheContinuationSet a b N n,
      Function.Injective (sixVertexBetheRootJacobian N n q.1 q.2)) :
    IsLocalHomeomorph
      (@sixVertexBetheContinuationProjection a b N n) := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  exact isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_rootJacobian
    ha hN hhalf Set.univ (fun q _ => hjac q.1 q.2)



def sixVertexBetheContinuationProjectionOn
    {a b : Real} {N n : Nat}
    (C : Set (SixVertexBetheContinuationSpace a b N n)) :
    C → Set.Icc a b :=
  fun q => sixVertexBetheContinuationProjection q.1

theorem continuous_sixVertexBetheContinuationProjectionOn
    {a b : Real} {N n : Nat}
    (C : Set (SixVertexBetheContinuationSpace a b N n)) :
    Continuous (sixVertexBetheContinuationProjectionOn C) :=
  continuous_sixVertexBetheContinuationProjection.comp continuous_subtype_val




theorem isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_rootJacobian
    {a b : Real} (ha : 2 < a) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N)
    (C : Set (SixVertexBetheContinuationSpace a b N n)) (hC : IsOpen C)
    (hjac : ∀ q ∈ C,
      Function.Injective (sixVertexBetheRootJacobian N n q.1.1 q.1.2)) :
    IsLocalHomeomorph (sixVertexBetheContinuationProjectionOn C) := by
  have hOn :=
    isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_rootJacobian
      ha hN hhalf C hjac
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  have hsub : IsLocalHomeomorphOn
      (Subtype.val : C → SixVertexBetheContinuationSpace a b N n)
      Set.univ :=
    hC.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
  have hcomp := hOn.comp hsub (fun q _ => q.2)
  simpa [sixVertexBetheContinuationProjectionOn, Function.comp_def] using hcomp




theorem exists_sixVertexContinuousBetheBranch_of_compactComponent
    {a b c₀ : Real} (hab : a ≤ b) (hc₀ : c₀ ∈ Set.Icc a b)
    {N n : Nat} (hN : 0 < N)
    (C : Set (SixVertexBetheContinuationSpace a b N n))
    (hcompact : IsCompact C)
    (hlocal : IsLocalHomeomorph
      (sixVertexBetheContinuationProjectionOn C))
    (z₀ : C)
    (hz₀ : sixVertexBetheContinuationProjectionOn C z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin n → Real),
      roots c₀ = z₀.1.1.2 ∧
      ∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N n (roots t) := by
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
  have hproj : Continuous (sixVertexBetheContinuationProjectionOn C) :=
    continuous_sixVertexBetheContinuationProjectionOn C
  have hcovOn : IsCoveringMapOn
      (sixVertexBetheContinuationProjectionOn C) Set.univ :=
    IsCoveringMapOn.of_openPartialHomeomorph hproj
      (fun e _ => by
        obtain ⟨phi, he, hphi⟩ := hlocal e
        exact ⟨phi, he, hphi.symm⟩)
  have hcov : IsCoveringMap (sixVertexBetheContinuationProjectionOn C) :=
    isCoveringMap_iff_isCoveringMapOn_univ.mpr hcovOn
  let clamp : Real → Set.Icc a b := fun t =>
    ⟨min b (max a t),
      ⟨le_min hab (le_max_left _ _), min_le_left _ _⟩⟩
  have hclamp : Continuous clamp :=
    Continuous.subtype_mk (by fun_prop) _
  let f : C(Real, Set.Icc a b) := ⟨clamp, hclamp⟩
  have hf₀ : f c₀ = sixVertexBetheContinuationProjectionOn C z₀ := by
    rw [hz₀]
    apply Subtype.ext
    simp [f, clamp, max_eq_right hc₀.1, min_eq_right hc₀.2]
  letI : ContractibleSpace Real :=
    (contractible_iff_id_nullhomotopic Real).mpr
      ⟨0, ⟨ContinuousMap.Homotopy.affine
        (ContinuousMap.id Real) (ContinuousMap.const Real 0)⟩⟩
  obtain ⟨F, hF₀, hFlift⟩ :=
    (hcov.existsUnique_continuousMap_lifts f c₀ z₀ hf₀.symm).exists
  let roots : C(Real, Fin n → Real) :=
    ⟨fun t => (F t).1.1.2,
      continuous_subtype_val.snd.comp
        (continuous_subtype_val.comp F.continuous)⟩
  refine ⟨roots, ?_, ?_⟩
  · change (F c₀).1.1.2 = z₀.1.1.2
    rw [hF₀]
  · intro t ht
    have hprojF := congrFun hFlift t
    have hclamp_t : f t = ⟨t, ht⟩ := by
      apply Subtype.ext
      simp [f, clamp, max_eq_right ht.1, min_eq_right ht.2]
    have hfirst : (F t).1.1.1 = t := by
      have h := congrArg Subtype.val hprojF
      simpa [hclamp_t, sixVertexBetheContinuationProjectionOn,
        sixVertexBetheContinuationProjection] using h
    have hmem := (F t).1.2
    have hfix : sixVertexBetheUpdate t N n (F t).1.1.2 =
        (F t).1.1.2 := by
      calc
        sixVertexBetheUpdate t N n (F t).1.1.2 =
            sixVertexBetheUpdate (F t).1.1.1 N n (F t).1.1.2 := by
          exact congrArg
            (fun s => sixVertexBetheUpdate s N n (F t).1.1.2) hfirst.symm
        _ = (F t).1.1.2 := hmem.2.2
    exact (sixVertexBetheUpdate_eq_self_iff hN _).mp hfix



theorem exists_sixVertexContinuousBetheBranch_of_regularComponent
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N)
    (C : Set (SixVertexBetheContinuationSpace a b N n))
    (hCopen : IsOpen C) (hCcompact : IsCompact C)
    (hjac : ∀ q ∈ C,
      Function.Injective (sixVertexBetheRootJacobian N n q.1.1 q.1.2))
    (z₀ : C)
    (hz₀ : sixVertexBetheContinuationProjectionOn C z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin n → Real),
      roots c₀ = z₀.1.1.2 ∧
      ∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N n (roots t) :=
  exists_sixVertexContinuousBetheBranch_of_compactComponent hab hc₀ hN C
    hCcompact
    (isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_rootJacobian
      ha hN hhalf C hCopen hjac)
    z₀ hz₀





theorem exists_sixVertexContinuousBetheBranch_of_rootJacobian
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N)
    (hjac : ∀ q ∈ sixVertexBetheContinuationSet a b N n,
      Function.Injective (sixVertexBetheRootJacobian N n q.1 q.2))
    (z₀ : SixVertexBetheContinuationSpace a b N n)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin n → Real),
      roots c₀ = z₀.1.2 ∧
      ∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N n (roots t) :=
  exists_sixVertexContinuousBetheBranch_of_isLocalHomeomorph
    ha hab hc₀ hN
      (isLocalHomeomorph_sixVertexBetheContinuationProjection_of_rootJacobian
        ha hN hhalf hjac)
    z₀ hz₀

end

end StatMech.FrontierD
