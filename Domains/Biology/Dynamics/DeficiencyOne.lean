/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.Dynamics.DeficiencyZero.API
public import MathlibExt.Dynamics.PolynomialNetworks.LinkageClass
public import Domains.Biology.Dynamics.DeficiencyZero.RankIdentities
public import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Deficiency one: linkage-class deficiencies and the decoupled equilibrium equations

Feinberg's deficiency-one theorem concerns a mass-action network
`N : ReactionNetwork S ρ` whose linkage classes `θ` (connected components of the undirected
reaction graph, `Domains.Biology.Dynamics.DeficiencyZero.API`) each have their own
deficiency `δ_θ = n_θ - 1 - s_θ`: `n_θ` complexes in the class and `s_θ` the dimension of
the span `𝒮_θ` of the reaction vectors of the reactions in the class. Its hypotheses are

1. `δ_θ ≤ 1` for every linkage class,
2. `∑_θ δ_θ = δ`, and
3. each linkage class contains exactly one terminal strong linkage class.

Its conclusion is that for every choice of positive rate constants, each positive
stoichiometric compatibility class contains at most one positive equilibrium, and exactly one
when the network is weakly reversible.

This file proves the linear-algebra part of the theorem for finite networks (`[Finite S]`,
`[Finite ρ]`, and finitely many linkage classes): what hypothesis 2 says and what it
does to the equilibrium equations. The stoichiometric subspace is always the sum
`𝒮 = ∑_θ 𝒮_θ`, so `∑_θ δ_θ ≤ δ`. Under these finiteness hypotheses, equality holds exactly when
the sum is direct, and then the mass-action field vanishes iff its restriction to each linkage
class does, so the equilibrium equations decouple across linkage classes (Feinberg 1995; Boros
2012).

## Main definitions

These are defined in `MathlibExt.Dynamics.PolynomialNetworks.LinkageClass`:

* `linkageClassOf r`: the linkage class of the reaction `r` (that of its source complex);
* `linkageClassNetwork θ`: the reactions of the linkage class `θ`, as a network on `S`;
* `linkageClassStoichiometricSubspace θ`: the span `𝒮_θ` of their reaction vectors;
* `linkageClassDeficiency θ`: for finitely many complexes (`[Finite N.complexes]`),
  `δ_θ = n_θ - 1 - s_θ`;
* `linkageClassField θ k x`: for finite species (`[Fintype S]`) and finite reactions
  (`[Fintype ρ]`), the part
  `∑_{r : ρ, linkageClassOf r = θ} k r (∏_{s : S} x_s ^ (src r s)) (prod r - src r)` of the
  mass-action field contributed by the reactions of `θ`.

## Main results

* `stoichiometricSubspace_eq_iSup`: `𝒮 = ⨆ θ, 𝒮_θ`.
* `linkageClassDeficiency_nonneg`: `0 ≤ δ_θ`.
* `deficiency_sub_sum_linkageClassDeficiency`: `δ - ∑_θ δ_θ = ∑_θ s_θ - s`.
* `sum_linkageClassDeficiency_le`: `∑_θ δ_θ ≤ δ`.
* `sum_linkageClassDeficiency_eq_iff`: `∑_θ δ_θ = δ` iff the `𝒮_θ` are independent
  (`iSupIndep`).
* `linkageClassDeficiency_le_deficiency`, `linkageClassDeficiency_eq_zero_of_deficiency_eq_zero`,
  `sum_linkageClassDeficiency_eq_of_deficiency_eq_zero`: a deficiency-zero network has
  `δ_θ = 0` for every linkage class and `∑_θ δ_θ = δ`, so it satisfies hypotheses 1 and 2.
* `sum_linkageClassField`, `linkageClassField_mem`: the mass-action field is the sum of the
  linkage-class fields, and the field of `θ` lies in `𝒮_θ`.
* `massActionField_eq_zero_iff_of_sum_linkageClassDeficiency_eq`: if `∑_θ δ_θ = δ`, then for
  all real `k` and `x`, `x` is an equilibrium iff every linkage-class field vanishes at `x`.

## Not covered

Terminal strong linkage classes (hypothesis 3) are not defined here, and neither conclusion of
the deficiency-one theorem is proved: not uniqueness of positive equilibria in a
stoichiometric compatibility class, and not existence in the weakly reversible case.
Uniqueness needs the general kernel theory of the Laplacian of the weighted reaction digraph:
its kernel is spanned by nonnegative vectors supported on the terminal strong linkage classes,
one per class. The weakly reversible case has a positive kernel vector, as shown in
`Domains.Biology.Dynamics.DeficiencyZero.Existence`.

## References

* M. Feinberg, "Chemical reaction network structure and the stability of complex isothermal
  reactors — I. The deficiency zero and deficiency one theorems", Chem. Eng. Sci. 42 (1987)
  2229–2268.
* M. Feinberg, "The existence and uniqueness of steady states for a class of chemical reaction
  networks", Arch. Rational Mech. Anal. 132 (1995) 311–370.
* B. Boros, "Notes on the deficiency-one theorem: multiple linkage classes", Math. Biosci. 235
  (2012) 110–122.
* M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019).
-/

@[expose] public section

open Finset Module

namespace MathlibExt.Biology.Dynamics.ComplexBalanced

variable {S ρ : Type*}

namespace ReactionNetwork

variable {N : ReactionNetwork S ρ}

/-! ### Reactions and linkage classes -/

theorem src_mem_supp_linkageClassOf (r : ρ) :
    (⟨N.src r, src_mem_complexes r⟩ : N.complexes) ∈ (N.linkageClassOf r).supp :=
  rfl

/-- The product complex of a reaction lies in the linkage class of the reaction. -/
theorem linkageClassOf_prod (r : ρ) :
    N.linkageGraph.connectedComponentMk ⟨N.prod r, prod_mem_complexes r⟩ = N.linkageClassOf r :=
  SimpleGraph.ConnectedComponent.eq.2 (src_reachable_prod r).symm

/-- A reaction whose source is a complex of `θ` belongs to `θ`. -/
theorem linkageClassOf_eq_of_src_mem {θ : N.linkageGraph.ConnectedComponent} {r : ρ}
    {c : N.complexes} (hc : c ∈ θ.supp) (hr : N.src r = c) : N.linkageClassOf r = θ := by
  have : (⟨N.src r, src_mem_complexes r⟩ : N.complexes) = c := Subtype.ext hr
  rw [linkageClassOf, this]
  exact hc

/-- A reaction whose product is a complex of `θ` belongs to `θ`. -/
theorem linkageClassOf_eq_of_prod_mem {θ : N.linkageGraph.ConnectedComponent} {r : ρ}
    {c : N.complexes} (hc : c ∈ θ.supp) (hr : N.prod r = c) : N.linkageClassOf r = θ := by
  have : (⟨N.prod r, prod_mem_complexes r⟩ : N.complexes) = c := Subtype.ext hr
  rw [← linkageClassOf_prod, this]
  exact hc

/-! ### The stoichiometric subspace is the sum of the linkage-class subspaces -/

theorem linkageClassStoichiometricSubspace_eq (θ : N.linkageGraph.ConnectedComponent) :
    N.linkageClassStoichiometricSubspace θ =
      Submodule.span ℝ (Set.range fun r : {r // N.linkageClassOf r = θ} =>
        fun s => (N.prod r s : ℝ) - N.src r s) :=
  rfl

/-- The reaction vector of a reaction of `θ` lies in `𝒮_θ`. -/
theorem reactionVector_mem_linkageClassStoichiometricSubspace
    {θ : N.linkageGraph.ConnectedComponent} {r : ρ} (hr : N.linkageClassOf r = θ) :
    (fun s => (N.prod r s : ℝ) - N.src r s) ∈ N.linkageClassStoichiometricSubspace θ :=
  Submodule.subset_span ⟨⟨r, hr⟩, rfl⟩

theorem linkageClassStoichiometricSubspace_le (θ : N.linkageGraph.ConnectedComponent) :
    N.linkageClassStoichiometricSubspace θ ≤ N.stoichiometricSubspace :=
  Submodule.span_mono fun _ ⟨r, hr⟩ => ⟨r.1, hr⟩

/-- **The stoichiometric subspace is the sum of the linkage-class stoichiometric subspaces**,
`𝒮 = ∑_θ 𝒮_θ`.

Source: Feinberg (1987). -/
theorem stoichiometricSubspace_eq_iSup :
    N.stoichiometricSubspace = ⨆ θ, N.linkageClassStoichiometricSubspace θ := by
  refine le_antisymm (Submodule.span_le.2 ?_) (iSup_le linkageClassStoichiometricSubspace_le)
  rintro _ ⟨r, rfl⟩
  exact Submodule.mem_iSup_of_mem (N.linkageClassOf r)
    (reactionVector_mem_linkageClassStoichiometricSubspace rfl)

/-! ### Dimension of a finite sum of subspaces -/

/-- For finitely many subspaces `p i` of a finite-dimensional space, the summation map
`∏ i, p i → M` has range `⨆ i, p i`, so `dim (⨆ i, p i) + dim (ker) = ∑ i, dim (p i)`, and its
kernel is trivial iff the `p i` are independent. -/
private lemma finrank_iSup_add_finrank_ker {ι M : Type*} [Fintype ι] [AddCommGroup M]
    [Module ℝ M] [FiniteDimensional ℝ M] (p : ι → Submodule ℝ M) :
    ∃ L : (∀ i, p i) →ₗ[ℝ] M,
      finrank ℝ ↥(⨆ i, p i) + finrank ℝ (LinearMap.ker L) = ∑ i, finrank ℝ (p i) ∧
        (LinearMap.ker L = ⊥ ↔ iSupIndep p) := by
  classical
  let L : (∀ i, p i) →ₗ[ℝ] M := ∑ i, (p i).subtype ∘ₗ LinearMap.proj i
  have hL : ∀ v, L v = ∑ i, (v i : M) := fun v => by simp [L]
  have hrange : LinearMap.range L = ⨆ i, p i := by
    refine le_antisymm ?_ (iSup_le fun i x hx => ⟨Pi.single i ⟨x, hx⟩, ?_⟩)
    · rintro _ ⟨v, rfl⟩
      rw [hL]
      exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i (v i).2
    · rw [hL, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj]; rfl)
        (fun h => absurd (mem_univ i) h), Pi.single_eq_same]
  refine ⟨L, ?_, ?_⟩
  · rw [← hrange, LinearMap.finrank_range_add_finrank_ker, Module.finrank_pi_fintype]
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero, LinearMap.ker_eq_bot']
    constructor
    · intro h s v hv hsum i hi
      let u : ∀ j, p j := fun j => if hj : j ∈ s then ⟨v j, hv j hj⟩ else 0
      have hu : ∀ j, (u j : M) = if j ∈ s then v j else 0 := fun j => by
        by_cases hj : j ∈ s <;> simp [u, hj]
      have hu0 : u = 0 := h u (by rw [hL]; simp_rw [hu]; rw [Finset.sum_ite_mem,
        Finset.univ_inter, hsum])
      exact (by simpa [hu0, hi] using hu i : (0 : M) = v i).symm
    · intro h v hv
      rw [hL] at hv
      funext i
      exact Subtype.ext (h univ (fun i => (v i : M)) (fun i _ => (v i).2) hv i (mem_univ i))

/-- For a network with finitely many species (`[Finite S]`) and finitely many linkage classes,
`dim (∑_θ 𝒮_θ) ≤ ∑_θ dim 𝒮_θ`, i.e. `s ≤ ∑_θ s_θ`. -/
theorem finrank_stoichiometricSubspace_le_sum [Finite S]
    [Fintype N.linkageGraph.ConnectedComponent] :
    finrank ℝ N.stoichiometricSubspace ≤
      ∑ θ, finrank ℝ (N.linkageClassStoichiometricSubspace θ) := by
  obtain ⟨L, hL, -⟩ := finrank_iSup_add_finrank_ker N.linkageClassStoichiometricSubspace
  rw [stoichiometricSubspace_eq_iSup]
  omega

/-- For a network with finitely many species (`[Finite S]`) and finitely many linkage classes,
`s = ∑_θ s_θ` holds iff the linkage-class stoichiometric subspaces are independent,
i.e. `𝒮 = ⊕_θ 𝒮_θ`. (Finiteness is required because `finrank` vanishes in infinite dimension.) -/
theorem finrank_stoichiometricSubspace_eq_sum_iff [Finite S]
    [Fintype N.linkageGraph.ConnectedComponent] :
    finrank ℝ N.stoichiometricSubspace =
        ∑ θ, finrank ℝ (N.linkageClassStoichiometricSubspace θ) ↔
      iSupIndep N.linkageClassStoichiometricSubspace := by
  obtain ⟨L, hL, hind⟩ := finrank_iSup_add_finrank_ker N.linkageClassStoichiometricSubspace
  rw [stoichiometricSubspace_eq_iSup, ← hind, ← Submodule.finrank_eq_zero]
  omega

/-! ### Linkage-class deficiencies -/

/-- For a network with finitely many complexes (`[Finite N.complexes]`), and so finitely many
linkage classes, the number of complexes is the sum over the linkage classes of their numbers of
complexes. -/
theorem card_complexes_eq_sum [Finite N.complexes]
    [Fintype N.linkageGraph.ConnectedComponent] :
    Nat.card N.complexes = ∑ θ : N.linkageGraph.ConnectedComponent, Nat.card θ.supp := by
  rw [← Nat.card_sigma]
  exact Nat.card_congr (Equiv.sigmaFiberEquiv N.linkageGraph.connectedComponentMk).symm

/-- **Each linkage class has nonnegative deficiency**, `0 ≤ δ_θ`, for a network with finitely
many reactions (`[Finite ρ]`): Feinberg's rank identity `n - ℓ - s = dim (ker Y ∩ Δ)` applied to
the reactions of `θ`, whose linkage graph is connected.

Source: Feinberg (1987); Feinberg (2019). -/
theorem linkageClassDeficiency_nonneg [Finite ρ] (θ : N.linkageGraph.ConnectedComponent) :
    0 ≤ N.linkageClassDeficiency θ := by
  classical
  have := Fintype.ofFinite θ.supp
  let s : {r // N.linkageClassOf r = θ} → θ.supp := fun r =>
    ⟨⟨N.src r.1, src_mem_complexes r.1⟩, r.2⟩
  let t : {r // N.linkageClassOf r = θ} → θ.supp := fun r =>
    ⟨⟨N.prod r.1, prod_mem_complexes r.1⟩, (linkageClassOf_prod r.1).trans r.2⟩
  have hG : ∀ c c' : θ.supp, θ.toSimpleGraph.Adj c c' ↔
      c ≠ c' ∧ ∃ r, (s r = c ∧ t r = c') ∨ (s r = c' ∧ t r = c) := by
    intro c c'
    change N.linkageGraph.Adj c c' ↔ _
    rw [linkageGraph_adj]
    constructor
    · rintro ⟨hne, ⟨r, hr, hr'⟩ | ⟨r, hr, hr'⟩⟩
      · exact ⟨fun h => hne (congrArg Subtype.val h),
          ⟨r, linkageClassOf_eq_of_src_mem c.2 hr⟩,
          .inl ⟨Subtype.ext (Subtype.ext hr), Subtype.ext (Subtype.ext hr')⟩⟩
      · exact ⟨fun h => hne (congrArg Subtype.val h),
          ⟨r, linkageClassOf_eq_of_src_mem c'.2 hr⟩,
          .inr ⟨Subtype.ext (Subtype.ext hr), Subtype.ext (Subtype.ext hr')⟩⟩
    · rintro ⟨hne, r, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩
      · exact ⟨fun h => hne (Subtype.ext h),
          .inl ⟨r.1, congrArg (fun c : θ.supp => c.1.1) hs,
            congrArg (fun c : θ.supp => c.1.1) ht⟩⟩
      · exact ⟨fun h => hne (Subtype.ext h),
          .inr ⟨r.1, congrArg (fun c : θ.supp => c.1.1) hs,
            congrArg (fun c : θ.supp => c.1.1) ht⟩⟩
  have h := (N.linkageClassNetwork θ).card_sub_card_sub_finrank_nonneg
    (fun c : θ.supp => c.1.1) s t (fun _ => rfl) (fun _ => rfl) θ.toSimpleGraph hG
  have hconn := θ.connected_toSimpleGraph
  have h1 : Nat.card θ.toSimpleGraph.ConnectedComponent = 1 :=
    Nat.card_eq_one_iff_unique.2
      ⟨hconn.preconnected.subsingleton_connectedComponent,
        ⟨θ.toSimpleGraph.connectedComponentMk hconn.nonempty.some⟩⟩
  rw [h1, ← Nat.card_eq_fintype_card] at h
  exact h

/-- **Deficiency minus the sum of the linkage-class deficiencies**: for a network with finitely
many species (`[Finite S]`), finitely many reactions (`[Finite ρ]`), and finitely many linkage
classes, `δ - ∑_θ δ_θ = ∑_θ s_θ - s` in `ℤ`.

Source: Feinberg (1987). -/
theorem deficiency_sub_sum_linkageClassDeficiency [Finite S] [Finite ρ]
    [Fintype N.linkageGraph.ConnectedComponent] :
    N.deficiency - ∑ θ, N.linkageClassDeficiency θ =
      ∑ θ, (finrank ℝ (N.linkageClassStoichiometricSubspace θ) : ℤ) -
        finrank ℝ N.stoichiometricSubspace := by
  have hn : (Nat.card N.complexes : ℤ) =
      ∑ θ : N.linkageGraph.ConnectedComponent, (Nat.card θ.supp : ℤ) := by
    rw [card_complexes_eq_sum]
    push_cast
    rfl
  have hℓ : (N.numLinkageClasses : ℤ) = ∑ _θ : N.linkageGraph.ConnectedComponent, (1 : ℤ) := by
    simp [numLinkageClasses, Nat.card_eq_fintype_card]
  simp only [deficiency, linkageClassDeficiency, Finset.sum_sub_distrib]
  rw [hn, hℓ]
  ring

/-- **The linkage-class deficiencies sum to at most the deficiency**, `∑_θ δ_θ ≤ δ`, for a network
with finitely many species (`[Finite S]`), finitely many reactions (`[Finite ρ]`), and finitely
many linkage classes.

Source: Feinberg (1987); Feinberg (1995). -/
theorem sum_linkageClassDeficiency_le [Finite S] [Finite ρ]
    [Fintype N.linkageGraph.ConnectedComponent] :
    ∑ θ, N.linkageClassDeficiency θ ≤ N.deficiency := by
  have h := N.deficiency_sub_sum_linkageClassDeficiency
  have hle : (finrank ℝ N.stoichiometricSubspace : ℤ) ≤
      ∑ θ, (finrank ℝ (N.linkageClassStoichiometricSubspace θ) : ℤ) := by
    exact_mod_cast N.finrank_stoichiometricSubspace_le_sum
  linarith

/-- **`∑_θ δ_θ = δ` iff the linkage-class stoichiometric subspaces are independent**, i.e.
`𝒮 = ⊕_θ 𝒮_θ`, for a network with finitely many species (`[Finite S]`), finitely many reactions
(`[Finite ρ]`), and finitely many linkage classes. This is hypothesis 2 of the deficiency-one
theorem.

Source: Feinberg (1987); Feinberg (1995). -/
theorem sum_linkageClassDeficiency_eq_iff [Finite S] [Finite ρ]
    [Fintype N.linkageGraph.ConnectedComponent] :
    ∑ θ, N.linkageClassDeficiency θ = N.deficiency ↔
      iSupIndep N.linkageClassStoichiometricSubspace := by
  rw [← finrank_stoichiometricSubspace_eq_sum_iff]
  have h := N.deficiency_sub_sum_linkageClassDeficiency
  constructor
  · intro he
    have : ((finrank ℝ N.stoichiometricSubspace : ℕ) : ℤ) =
        ((∑ θ, finrank ℝ (N.linkageClassStoichiometricSubspace θ) : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this
  · intro he
    have : ((finrank ℝ N.stoichiometricSubspace : ℕ) : ℤ) =
        ((∑ θ, finrank ℝ (N.linkageClassStoichiometricSubspace θ) : ℕ) : ℤ) := by
      rw [he]
    push_cast at this
    linarith

/-- For a network with finitely many species (`[Finite S]`) and finitely many reactions
(`[Finite ρ]`), the deficiency of a linkage class is at most the deficiency of the network. -/
theorem linkageClassDeficiency_le_deficiency [Finite S] [Finite ρ]
    (θ : N.linkageGraph.ConnectedComponent) : N.linkageClassDeficiency θ ≤ N.deficiency :=
  have := Fintype.ofFinite N.linkageGraph.ConnectedComponent
  (Finset.single_le_sum (fun θ _ => linkageClassDeficiency_nonneg θ) (mem_univ θ)).trans
    sum_linkageClassDeficiency_le

/-- In a network of deficiency zero with finitely many species (`[Finite S]`) and finitely many
reactions (`[Finite ρ]`), every linkage class has deficiency zero. -/
theorem linkageClassDeficiency_eq_zero_of_deficiency_eq_zero [Finite S] [Finite ρ]
    (h : N.deficiency = 0)
    (θ : N.linkageGraph.ConnectedComponent) : N.linkageClassDeficiency θ = 0 :=
  le_antisymm (h ▸ linkageClassDeficiency_le_deficiency θ) (linkageClassDeficiency_nonneg θ)

/-- A network of deficiency zero with finitely many species (`[Finite S]`), finitely many
reactions (`[Finite ρ]`), and finitely many linkage classes satisfies `∑_θ δ_θ = δ`: together
with `linkageClassDeficiency_eq_zero_of_deficiency_eq_zero`, it satisfies hypotheses 1 and 2 of
the deficiency-one theorem.

Source: Feinberg (1987). -/
theorem sum_linkageClassDeficiency_eq_of_deficiency_eq_zero [Finite S] [Finite ρ]
    [Fintype N.linkageGraph.ConnectedComponent] (h : N.deficiency = 0) :
    ∑ θ, N.linkageClassDeficiency θ = N.deficiency := by
  simp [linkageClassDeficiency_eq_zero_of_deficiency_eq_zero h, h]

/-! ### The equilibrium equations decouple across linkage classes -/

variable [Fintype S] [Fintype ρ]

/-- For a network with finite species set `S` (`[Fintype S]`), finite reaction set `ρ`
(`[Fintype ρ]`), and finitely many linkage classes, the mass-action field is the sum of the
linkage-class fields, for all real `k` and `x`. -/
theorem sum_linkageClassField [Fintype N.linkageGraph.ConnectedComponent] (k : ρ → ℝ) (x : S → ℝ) :
    ∑ θ, N.linkageClassField θ k x = N.massActionField k x := by
  classical
  funext s
  simp only [Finset.sum_apply, linkageClassField, massActionField]
  convert Finset.sum_fiberwise univ N.linkageClassOf
    (fun r => k r * (∏ s', x s' ^ N.src r s') * ((N.prod r s : ℝ) - N.src r s))

/-- For a network with finite species set `S` (`[Fintype S]`) and finite reaction set `ρ`
(`[Fintype ρ]`), and for all real `k` and `x`, the field of the linkage class `θ` takes values in
`𝒮_θ`. -/
theorem linkageClassField_mem (θ : N.linkageGraph.ConnectedComponent) (k : ρ → ℝ)
    (x : S → ℝ) : N.linkageClassField θ k x ∈ N.linkageClassStoichiometricSubspace θ := by
  classical
  have h : N.linkageClassField θ k x =
      ∑ r ∈ univ.filter (fun r => N.linkageClassOf r = θ),
        (k r * ∏ s', x s' ^ N.src r s') • fun s => (N.prod r s : ℝ) - N.src r s := by
    funext s
    simp only [linkageClassField, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h]
  exact Submodule.sum_mem _ fun r hr => Submodule.smul_mem _ _
    (reactionVector_mem_linkageClassStoichiometricSubspace (Finset.mem_filter.1 hr).2)

/-- **The equilibrium equations decouple across independent linkage classes.** For a network with
finite species set `S` (`[Fintype S]`) and finite reaction set `ρ` (`[Fintype ρ]`), if the
linkage-class stoichiometric subspaces are independent, then for all real rate constants `k` and
concentrations `x`, the mass-action field vanishes at `x` iff the field of every linkage class
vanishes at `x`. -/
theorem massActionField_eq_zero_iff_of_iSupIndep
    (h : iSupIndep N.linkageClassStoichiometricSubspace) {k : ρ → ℝ} {x : S → ℝ} :
    N.massActionField k x = 0 ↔ ∀ θ, N.linkageClassField θ k x = 0 := by
  have := Fintype.ofFinite N.linkageGraph.ConnectedComponent
  rw [← sum_linkageClassField]
  refine ⟨fun h0 θ => (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 h univ _
    (fun θ _ => linkageClassField_mem θ k x) h0 θ (mem_univ θ), fun h0 => ?_⟩
  simp [h0]

/-- **Under `∑_θ δ_θ = δ` the equilibrium equations decouple across linkage classes**: let the
network have finite species set `S` (`[Fintype S]`), finite reaction set `ρ` (`[Fintype ρ]`), and
finitely many linkage classes. For all real rate constants `k` and concentrations `x`, `x` is an
equilibrium of the mass-action system iff the field of every linkage class vanishes at `x`. This
is the reduction to single linkage classes on which the deficiency-one theorem rests.

Source: Feinberg (1995); Boros (2012); Feinberg (2019). -/
theorem massActionField_eq_zero_iff_of_sum_linkageClassDeficiency_eq
    [Fintype N.linkageGraph.ConnectedComponent]
    (h : ∑ θ, N.linkageClassDeficiency θ = N.deficiency) {k : ρ → ℝ} {x : S → ℝ} :
    N.massActionField k x = 0 ↔ ∀ θ, N.linkageClassField θ k x = 0 :=
  massActionField_eq_zero_iff_of_iSupIndep (sum_linkageClassDeficiency_eq_iff.1 h)

end ReactionNetwork

end MathlibExt.Biology.Dynamics.ComplexBalanced
