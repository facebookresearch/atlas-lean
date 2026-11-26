/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Topology.Algebra.Group.ProfiniteCosetSection
import MathlibExt.Topology.Algebra.Group.ProfiniteCosetLimit
import Mathlib.Order.Zorn
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Tactic.Push

/-!
# Continuous sections of arbitrary nested closed coset spaces

For closed subgroups `K≤H` of a compact Hausdorff totally disconnected topological group, the
projection `G/K → G/H` admits a continuous right inverse.

Compatible partial sections over intermediate closed subgroups are refined by reverse inclusion;
chain intersections use the coset inverse-limit theorem. Neither subgroup normality nor finite
relative index is required for this general section.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Topology

namespace QuotientGroup

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

@[simp]
private theorem cosetProjection_id (K : Subgroup G) :
    cosetProjection (show K ≤ K from le_rfl) =
      ContinuousMap.id (G ⧸ K) := by
  ext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rfl

@[simp]
private theorem cosetProjection_comp
    {K H L : Subgroup G} (hKH : K ≤ H) (hHL : H ≤ L) :
    (cosetProjection hHL).comp (cosetProjection hKH) =
      cosetProjection (hKH.trans hHL) := by
  ext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rfl

private structure SectionApproximation (K H : Subgroup G) where
  subgroup : Subgroup G
  lower : K ≤ subgroup
  upper : subgroup ≤ H
  closed : IsClosed (subgroup : Set G)
  sec : C(G ⧸ H, G ⧸ subgroup)
  rightInverse : Function.RightInverse sec (cosetProjection upper)

namespace SectionApproximation

variable {K H : Subgroup G}

private def Refines (A B : SectionApproximation K H) : Prop :=
  ∃ h : B.subgroup ≤ A.subgroup,
    (cosetProjection h).comp B.sec = A.sec

private instance : LE (SectionApproximation K H) := ⟨Refines⟩

private instance : Preorder (SectionApproximation K H) where
  le_refl A := by
    refine ⟨le_rfl, ?_⟩
    rw [cosetProjection_id]
    ext x
    rfl
  le_trans A B C hAB hBC := by
    obtain ⟨hBA, hsAB⟩ := hAB
    obtain ⟨hCB, hsBC⟩ := hBC
    refine ⟨hCB.trans hBA, ?_⟩
    rw [← cosetProjection_comp hCB hBA]
    rw [ContinuousMap.comp_assoc, hsBC, hsAB]

private theorem ext {A B : SectionApproximation K H}
    (hsub : A.subgroup = B.subgroup)
    (hsec : HEq A.sec B.sec) : A = B := by
  cases A
  cases B
  cases hsub
  cases hsec
  rfl

private instance : PartialOrder (SectionApproximation K H) where
  le_antisymm A B hAB hBA := by
    obtain ⟨hBsubA, hsecAB⟩ := hAB
    obtain ⟨hAsubB, _hsecBA⟩ := hBA
    have hsub : A.subgroup = B.subgroup := le_antisymm hAsubB hBsubA
    apply ext hsub
    cases A
    cases B
    dsimp at hsub ⊢
    subst hsub
    simp only [cosetProjection_id, ContinuousMap.id_comp] at hsecAB
    exact heq_of_eq hsecAB.symm

end SectionApproximation

variable {K H : Subgroup G}

private def chainSubgroups (c : Set (SectionApproximation K H)) :
    c → Subgroup G := fun A => A.1.subgroup

private theorem chainSubgroups_antitone
    (c : Set (SectionApproximation K H)) :
    Antitone (chainSubgroups c) := by
  intro A B hAB
  exact hAB.choose

private def chainSectionCone
    (c : Set (SectionApproximation K H)) :
    Cone (antitoneCosetSystem (chainSubgroups c)
      (chainSubgroups_antitone c)) where
  pt := TopCat.of (G ⧸ H)
  π :=
    { app := fun A => TopCat.ofHom A.unop.1.sec
      naturality := fun A B f => by
        have hBA : B.unop.1 ≤ A.unop.1 := leOfHom f.unop
        obtain ⟨_hsub, hsec⟩ := hBA
        ext q
        exact (DFunLike.congr_fun hsec q).symm }

private theorem exists_upperBound_of_nonempty_chain
    [IsTopologicalGroup G] [CompactSpace G]
    {c : Set (SectionApproximation K H)}
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ ub : SectionApproximation K H, ∀ A ∈ c, A ≤ ub := by
  let _ : Nonempty c := hne.to_subtype
  let _ : IsDirectedOrder c := ⟨hc.directedOn.directed_val⟩
  let S : c → Subgroup G := chainSubgroups c
  let hS : Antitone S := chainSubgroups_antitone c
  let hclosed : ∀ A : c, IsClosed (S A : Set G) := fun A => A.1.closed
  let hlim : IsLimit (iInfCosetCone S hS) :=
    iInfCosetConeIsLimit S hS hclosed
  let C : Cone (antitoneCosetSystem S hS) := chainSectionCone c
  let lift : TopCat.of (G ⧸ H) ⟶ TopCat.of (G ⧸ (⨅ A, S A)) :=
    hlim.lift C
  obtain ⟨A0, hA0⟩ := hne
  let A0c : c := ⟨A0, hA0⟩
  have hlower : K ≤ ⨅ A, S A := by
    rw [le_iInf_iff]
    intro A
    exact A.1.lower
  have hupper : (⨅ A, S A) ≤ H :=
    (iInf_le S A0c).trans A0c.1.upper
  have hclosedInf : IsClosed ((⨅ A, S A : Subgroup G) : Set G) := by
    rw [Subgroup.coe_iInf]
    exact isClosed_iInter fun A => hclosed A
  have hright : Function.RightInverse lift.hom
      (cosetProjection hupper) := by
    intro q
    have hfac := hlim.fac C (Opposite.op A0c)
    have hfacq := ConcreteCategory.congr_hom hfac q
    change cosetProjection (iInf_le S A0c) (lift q) =
      A0c.1.sec q at hfacq
    change cosetProjection hupper (lift q) = q
    have hcomp := cosetProjection_comp
      (iInf_le S A0c) A0c.1.upper
    have hcompq := DFunLike.congr_fun hcomp (lift q)
    calc
      cosetProjection hupper (lift q) =
          cosetProjection A0c.1.upper
            (cosetProjection (iInf_le S A0c) (lift q)) :=
        hcompq.symm
      _ = cosetProjection A0c.1.upper (A0c.1.sec q) :=
        congrArg _ hfacq
      _ = q := A0c.1.rightInverse q
  let ub : SectionApproximation K H :=
    { subgroup := ⨅ A, S A
      lower := hlower
      upper := hupper
      closed := hclosedInf
      sec := lift.hom
      rightInverse := hright }
  refine ⟨ub, fun A hA => ?_⟩
  let Ac : c := ⟨A, hA⟩
  refine ⟨iInf_le S Ac, ?_⟩
  apply ContinuousMap.ext
  intro q
  have hfac := hlim.fac C (Opposite.op Ac)
  exact ConcreteCategory.congr_hom hfac q

private def initialApproximation
    (hKH : K ≤ H) (hHclosed : IsClosed (H : Set G)) :
    SectionApproximation K H where
  subgroup := H
  lower := hKH
  upper := le_rfl
  closed := hHclosed
  sec := ContinuousMap.id (G ⧸ H)
  rightInverse := by
    intro q
    rw [cosetProjection_id]
    rfl

/-- **Continuous section between nested closed profinite coset spaces.** Let `G` be a compact
Hausdorff totally disconnected topological group. for closed subgroups `K≤H`, there is
continuous `s : G/H → G/K` satisfying `cosetProjection∘s=id_(G/H)`. No normality or
finite-index assumption is required. -/
theorem exists_continuous_section_of_closedSubgroup_le
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K H : Subgroup G) (hKH : K ≤ H)
    [hKclosed : IsClosed (K : Set G)]
    [hHclosed : IsClosed (H : Set G)] :
    ∃ s : C(G ⧸ H, G ⧸ K),
      Function.RightInverse s (cosetProjection hKH) := by
  let _ : Nonempty (SectionApproximation K H) :=
    ⟨initialApproximation hKH hHclosed⟩
  have hzorn : ∃ M : SectionApproximation K H, IsMax M :=
    zorn_le_nonempty (fun (c : Set (SectionApproximation K H)) hc hne =>
      exists_upperBound_of_nonempty_chain (G := G) (K := K) (H := H)
        hc hne)
  obtain ⟨M, hM⟩ := hzorn
  have hMK : M.subgroup = K := by
    apply le_antisymm
    swap
    · exact M.lower
    by_contra hnot
    have hne : K ≠ M.subgroup := fun heq => hnot (by rw [← heq])
    have hstrict : K < M.subgroup := lt_of_le_of_ne M.lower hne
    obtain ⟨x, hxM, hxK⟩ := IsConcreteLE.exists_of_lt hstrict
    let Kc : ClosedSubgroup G := ⟨K, hKclosed⟩
    have hKsInf := ProfiniteGrp.closedSubgroup_eq_sInf_open Kc
    have hexists : ∃ L : Subgroup G,
        (IsOpen (L : Set G) ∧ K ≤ L) ∧ x ∉ L := by
      by_contra hn
      push Not at hn
      have hxInf :
          x ∈ sInf {L : Subgroup G | IsOpen (L : Set G) ∧ K ≤ L} :=
        Subgroup.mem_sInf.mpr fun L hL => hn L hL
      have hxK' : x ∈ K := by
        have hKsInf' : K =
            sInf {L : Subgroup G | IsOpen (L : Set G) ∧ K ≤ L} := by
          simpa [Kc] using hKsInf
        rw [hKsInf']
        exact hxInf
      exact hxK hxK'
    obtain ⟨L, ⟨hLopen, hKL⟩, hxL⟩ := hexists
    let T : Subgroup G := M.subgroup ⊓ L
    have hKT : K ≤ T := le_inf M.lower hKL
    have hTS : T ≤ M.subgroup := inf_le_left
    have hTclosed : IsClosed (T : Set G) :=
      M.closed.inter (Subgroup.isClosed_of_isOpen L hLopen)
    have hTne : T ≠ M.subgroup := by
      intro heq
      have hxT : x ∈ T := heq ▸ hxM
      exact hxL hxT.2
    have hTfinite : T.IsFiniteRelIndex M.subgroup := by
      rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
      let _ : CompactSpace M.subgroup :=
        isCompact_iff_compactSpace.mp M.closed.isCompact
      have hopen : IsOpen
          ((T.subgroupOf M.subgroup : Subgroup M.subgroup) :
            Set M.subgroup) := by
        change IsOpen (M.subgroup.subtype ⁻¹' (T : Set G))
        have heqpre : M.subgroup.subtype ⁻¹' (T : Set G) =
            M.subgroup.subtype ⁻¹' (L : Set G) := by
          ext y
          simp [T]
        rw [heqpre]
        exact hLopen.preimage continuous_subtype_val
      let _ : Finite
          (M.subgroup ⧸ (T.subgroupOf M.subgroup)) :=
        (T.subgroupOf M.subgroup).quotient_finite_of_isOpen hopen
      exact Subgroup.finiteIndex_of_finite_quotient
    let _ : IsClosed (T : Set G) := hTclosed
    let _ : IsClosed (M.subgroup : Set G) := M.closed
    let _ : T.IsFiniteRelIndex M.subgroup := hTfinite
    obtain ⟨r, hr⟩ :=
      exists_continuous_section_of_isFiniteRelIndex T M.subgroup hTS
    let R : SectionApproximation K H :=
      { subgroup := T
        lower := hKT
        upper := hTS.trans M.upper
        closed := hTclosed
        sec := r.comp M.sec
        rightInverse := by
          intro q
          have hcomp := cosetProjection_comp hTS M.upper
          have hcompq := DFunLike.congr_fun hcomp (r (M.sec q))
          calc
            cosetProjection (hTS.trans M.upper) (r (M.sec q)) =
                cosetProjection M.upper
                  (cosetProjection hTS (r (M.sec q))) :=
              hcompq.symm
            _ = cosetProjection M.upper (M.sec q) :=
              congrArg _ (hr (M.sec q))
            _ = q := M.rightInverse q }
    have hMR : M ≤ R := by
      refine ⟨hTS, ?_⟩
      apply ContinuousMap.ext
      intro q
      exact hr (M.sec q)
    have hRM := hM hMR
    have hMleT : M.subgroup ≤ T := hRM.choose
    exact hTne (le_antisymm hTS hMleT)
  cases M with
  | mk S lower upper closed sec rightInverse =>
      dsimp at hMK
      subst S
      exact ⟨sec, rightInverse⟩

end QuotientGroup

end
