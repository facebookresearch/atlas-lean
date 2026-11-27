/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.GroupTheory.FiniteIndexNormalSubgroup

@[expose] public section

/-!
# Strong completeness of profinite groups

A topological group is *strongly complete* when every finite-index subgroup is
open. For a profinite group `P`, strong completeness of its underlying
topological group is equivalent to bijectivity of Mathlib's canonical map
`ProfiniteGrp.ProfiniteCompletion.etaFn` into its profinite completion.
This is the new content of ATLAS `NumberTheoryI` Corollary 26.20, stated with
Mathlib's canonical profinite completion instead of an abstract one.

## Source correspondence

The source is Andrew V. Sutherland, *18.785 Number Theory I*, Lecture 26,
[Corollary 26.20](https://math.mit.edu/classes/18.785/2021fa/LectureNotes26.pdf#page=6).
It says that a profinite group `G` is naturally its topological inverse limit over open normal
subgroups, and that `G` is isomorphic to its profinite completion as an abstract group
(strong completeness) exactly when every finite-index subgroup is open.

The Lean declarations encode the second assertion clause by clause.

* A value `P : ProfiniteGrp` packages the source's profinite topological group.  The type
  `GrpCat.of ↑P` deliberately forgets its topology, so Mathlib's
  `ProfiniteCompletion.completion (GrpCat.of ↑P)` is the source's profinite completion
  “as a group,” indexed by all finite-index normal subgroups rather than only the open ones.
* `ProfiniteCompletion.etaFn (GrpCat.of ↑P)` is the underlying function of the
  canonical homomorphism `G → Ĝ`.  Because it is already a group homomorphism,
  `Function.Bijective` is exactly the source's “isomorphic as a group.”
* `IsStronglyComplete ↑P` states verbatim that every finite-index subgroup of `G` is
  open.  The reverse implication passes from an arbitrary finite-index subgroup to its
  finite-index normal core, matching the standard reduction implicit in the source proof.
* The forward implication uses compactness of `P` and the finite-intersection property to
  prove surjectivity; injectivity uses the separating open normal subgroups of a profinite
  group.  Conversely, surjectivity makes every finite-index normal subgroup closed, hence
  open, and the normal-core reduction handles all finite-index subgroups.

The standalone definition `IsStronglyComplete` applies to any topological group; the
characterization itself retains precisely the source hypothesis `P : ProfiniteGrp`.
The source's first, topological inverse-limit assertion is background supplied by the
`ProfiniteGrp`/completion API and is not claimed as a new theorem here.
-/

/-- **Strongly complete group.** A group $G$ equipped with a topology is *strongly complete* when
every subgroup of finite index in $G$ is open. -/
def IsStronglyComplete (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ H : Subgroup G, H.FiniteIndex → IsOpen (H : Set G)

namespace ProfiniteGrp.ProfiniteCompletion

open CategoryTheory CategoryTheory.Limits

universe u

variable (P : ProfiniteGrp.{u})

/-- **Finite-index normal subgroups are closed when the completion map is onto.** Let $P$ be a
profinite group and let $\hat P$ be the profinite completion of $P$ as an abstract group, that is,
the inverse limit of the finite quotients $P/N$ over all normal subgroups $N$ of finite index in
$P$. If the canonical map $P \to \hat P$ is surjective, then every normal subgroup of finite
index in $P$ is closed in $P$. -/
theorem isClosed_toSubgroup_of_surjective_etaFn
    (N : FiniteIndexNormalSubgroup (GrpCat.of ↥P))
    (hsurj : Function.Surjective (etaFn (GrpCat.of ↥P))) :
    IsClosed (N.toSubgroup : Set ↥P) := by
  let ψ : completion (GrpCat.of ↥P) ⟶ P :=
    lift (GrpCat.ofHom (MonoidHom.id (GrpCat.of ↥P)))
  have hψ : ∀ g : ↥P, ψ (etaFn (GrpCat.of ↥P) g) = g := by
    intro g
    have h := lift_eta (GrpCat.ofHom (MonoidHom.id (GrpCat.of ↥P)) :
      GrpCat.of ↥P ⟶ GrpCat.of ↥P)
    exact DFunLike.congr_fun (congrArg (fun f => f.hom) h) g
  let πN := (limitCone (diagram (GrpCat.of ↥P))).π.app N
  have hN_eq : (N.toSubgroup : Set ↥P) = ψ '' {x | πN x = 1} := by
    ext g
    constructor
    · intro hg
      refine ⟨etaFn (GrpCat.of ↥P) g, ?_, hψ g⟩
      exact (QuotientGroup.eq_one_iff g).mpr hg
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨g', rfl⟩ := hsurj x
      rw [hψ g']
      exact (QuotientGroup.eq_one_iff g').mp hx
  rw [hN_eq]
  exact (isClosed_singleton.preimage πN.hom.continuous_toFun).isCompact.image
    ψ.hom.continuous_toFun |>.isClosed

/-- **Finite-index normal subgroups are open when the completion map is onto.** Let $P$ be a
profinite group and let $\hat P$ be the profinite completion of $P$ as an abstract group, that is,
the inverse limit of the finite quotients $P/N$ over all normal subgroups $N$ of finite index in
$P$. If the canonical map $P \to \hat P$ is surjective, then every normal subgroup of finite
index in $P$ is open in $P$. -/
theorem isOpen_toSubgroup_of_surjective_etaFn
    (N : FiniteIndexNormalSubgroup (GrpCat.of ↥P))
    (hsurj : Function.Surjective (etaFn (GrpCat.of ↥P))) :
    IsOpen (N.toSubgroup : Set ↥P) :=
  N.toSubgroup.isOpen_of_isClosed_of_finiteIndex
    (isClosed_toSubgroup_of_surjective_etaFn P N hsurj)

/-- **Strongly complete profinite groups via the profinite completion.** Let $P$ be a profinite
group and let $\hat P$ be the profinite completion of $P$ as an abstract group, that is, the
inverse limit of the finite quotients $P/N$ over all normal subgroups $N$ of finite index in $P$.
Then $P$ is strongly complete if and only if the canonical map $P \to \hat P$ is bijective. -/
theorem isStronglyComplete_iff_bijective_etaFn :
    IsStronglyComplete ↥P ↔ Function.Bijective (etaFn (GrpCat.of ↥P)) := by
  constructor
  · intro hsc
    refine ⟨?_, ?_⟩
    · have hker : (eta (GrpCat.of ↥P)).hom.ker = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro d hd
        by_contra hne
        obtain ⟨U, hU⟩ :=
          ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
            isOpen_compl_singleton
            (Set.mem_compl_singleton_iff.mpr (fun h : (1 : ↥P) = d => hne h.symm))
        have hfin : Finite (↥P ⧸ (U : Subgroup ↥P)) :=
          (U : Subgroup ↥P).quotient_finite_of_isOpen U.toOpenSubgroup.isOpen'
        have hFI : (U : Subgroup ↥P).FiniteIndex :=
          @Subgroup.finiteIndex_of_finite_quotient _ _ _ hfin
        have hN : (U : Subgroup ↥P).Normal := U.isNormal'
        let N : FiniteIndexNormalSubgroup (GrpCat.of ↥P) :=
          { toSubgroup := (U : Subgroup ↥P), isNormal' := hN,
            isFiniteIndex' := hFI }
        have hmem : (eta (GrpCat.of ↥P)).hom d = 1 := MonoidHom.mem_ker.mp hd
        have h1 : ((limitCone (diagram (GrpCat.of ↥P))).π.app N) ((eta _).hom d)
            = 1 := by
          rw [hmem]
          exact ((limitCone (diagram (GrpCat.of ↥P))).π.app N).hom.map_one
        have hdU : d ∈ (U : Subgroup ↥P) := (QuotientGroup.eq_one_iff d).mp h1
        exact absurd (hU hdU) (by simp)
      exact (eta (GrpCat.of ↥P)).hom.ker_eq_bot_iff.mp hker
    · intro c
      have hC_nonempty : ∀ N : FiniteIndexNormalSubgroup (GrpCat.of ↥P),
          (QuotientGroup.mk' N.toSubgroup ⁻¹' {c.val N}).Nonempty := by
        intro N
        obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N.toSubgroup (c.val N)
        exact ⟨g, hg⟩
      have hC_closed : ∀ N : FiniteIndexNormalSubgroup (GrpCat.of ↥P),
          IsClosed (QuotientGroup.mk' N.toSubgroup ⁻¹' {c.val N}) := by
        intro N
        have hNopen : IsOpen (N.toSubgroup : Set ↥P) := hsc N.toSubgroup N.isFiniteIndex'
        let _ : DiscreteTopology (↥P ⧸ N.toSubgroup) :=
          QuotientGroup.discreteTopology hNopen
        exact IsClosed.preimage continuous_quotient_mk' isClosed_singleton
      have hC_directed : Directed (· ⊇ ·)
          (fun N : FiniteIndexNormalSubgroup (GrpCat.of ↥P) =>
            QuotientGroup.mk' N.toSubgroup ⁻¹' {c.val N}) := by
        intro N₁ N₂
        let N₃ : FiniteIndexNormalSubgroup (GrpCat.of ↥P) :=
          { toSubgroup := N₁.toSubgroup ⊓ N₂.toSubgroup,
            isNormal' := Subgroup.normal_inf_normal N₁.toSubgroup N₂.toSubgroup }
        refine ⟨N₃, ?_, ?_⟩
        · intro g hg
          change QuotientGroup.mk' N₃.toSubgroup g = c.val N₃ at hg
          change QuotientGroup.mk' N₁.toSubgroup g = c.val N₁
          have hsub13 : N₃.toSubgroup ≤ N₁.toSubgroup := inf_le_left
          have h13 : N₃ ≤ N₁ := hsub13
          have hcomp := c.property (homOfLE h13)
          rw [← hg] at hcomp
          rw [← hcomp]
          change QuotientGroup.mk' N₁.toSubgroup g =
            QuotientGroup.map N₃.toSubgroup N₁.toSubgroup (MonoidHom.id _) hsub13
              (QuotientGroup.mk' N₃.toSubgroup g)
          exact (QuotientGroup.map_mk' (N := N₃.toSubgroup) N₁.toSubgroup
            (MonoidHom.id _) hsub13 g).symm
        · intro g hg
          change QuotientGroup.mk' N₃.toSubgroup g = c.val N₃ at hg
          change QuotientGroup.mk' N₂.toSubgroup g = c.val N₂
          have hsub23 : N₃.toSubgroup ≤ N₂.toSubgroup := inf_le_right
          have h23 : N₃ ≤ N₂ := hsub23
          have hcomp := c.property (homOfLE h23)
          rw [← hg] at hcomp
          rw [← hcomp]
          change QuotientGroup.mk' N₂.toSubgroup g =
            QuotientGroup.map N₃.toSubgroup N₂.toSubgroup (MonoidHom.id _) hsub23
              (QuotientGroup.mk' N₃.toSubgroup g)
          exact (QuotientGroup.map_mk' (N := N₃.toSubgroup) N₂.toSubgroup
            (MonoidHom.id _) hsub23 g).symm
      let _ : Nonempty (FiniteIndexNormalSubgroup (GrpCat.of ↥P)) :=
        ⟨{ toSubgroup := ⊤ }⟩
      obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        _ hC_directed hC_nonempty (fun N => (hC_closed N).isCompact) hC_closed
      refine ⟨g, Subtype.ext (funext fun N => ?_)⟩
      have hgN := Set.mem_iInter.mp hg N
      simp only [Set.mem_preimage] at hgN
      exact hgN
  · intro hbij H hH
    have hFI : H.FiniteIndex := hH
    have hcoreFI : H.normalCore.FiniteIndex :=
      @Subgroup.finiteIndex_normalCore _ _ H hFI
    suffices hopen : IsOpen (H.normalCore : Set ↥P) from
      Subgroup.isOpen_mono H.normalCore_le hopen
    have hcoreN : H.normalCore.Normal := Subgroup.normalCore_normal H
    exact isOpen_toSubgroup_of_surjective_etaFn P
      (@FiniteIndexNormalSubgroup.ofSubgroup _ _ H.normalCore hcoreN hcoreFI) hbij.2

end ProfiniteCompletion

end ProfiniteGrp
