/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.ComplexBalanced
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank and linkage identities for the deficiency of a reaction network

Let a reaction network on species `S` have complexes indexed by a finite type `K`, with
`y c : S → ℕ` the composition of complex `c`, and let reaction `r` go from complex `s r` to
complex `t r` (so `src r = y (s r)` and `prod r = y (t r)`). Its linkage classes are the
connected components of the undirected reaction graph `G` on `K`. Write
`Δ = span {e_{t r} - e_{s r}} ⊆ ℝ^K` for the span of the reaction vectors in complex space and
`Y : ℝ^K → ℝ^S`, `e_c ↦ y c`, for the complex-composition map. The deficiency is
`δ = n - ℓ - s` with `n = #K`, `ℓ` the number of linkage classes and
`s = dim (stoichiometric subspace)`.

## Main results

* `DeficiencyZero.finrank_span_incidence_eq`: `dim Δ = n - ℓ`. The proof identifies the
  annihilator of `Δ` with the kernel of the graph Laplacian of `G` and uses Mathlib's
  `SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`
  (the kernel of the Laplacian has dimension `ℓ`).
* `ReactionNetwork.stoichiometricSubspace_eq_map`: the stoichiometric subspace is `Y Δ`.
* `ReactionNetwork.rank_stoichiometricMatrix_eq_finrank`: the rank of the stoichiometric
  matrix `Γ` (columns `prod r - src r`) is `s`.
* `ReactionNetwork.card_sub_card_sub_finrank_eq_finrank_ker_inf`:
  `n - ℓ - s = dim (ker Y ∩ Δ)` (Feinberg's characterization of the deficiency), hence
  `card_sub_card_sub_finrank_nonneg` (`δ ≥ 0`), `card_sub_card_sub_finrank_eq_zero_iff`
  (`δ = 0 ↔ ker Y ∩ Δ = 0`) and `card_sub_card_sub_finrank_eq_zero_of_linearIndependent`
  (linearly independent complex compositions give `δ = 0`).
* `ReactionNetwork.complexes_linkage_finrank_nonneg`, `complexes_linkage_rank_nonneg` and
  `complexes_linkage_finrank_eq_zero_of_linearIndependent` restate these for the complexes
  `Set.range src ∪ Set.range prod` and the linkage graph
  `SimpleGraph.fromRel (fun c c' => ∃ r, src r = c ∧ prod r = c')`, i.e. for the exact
  unfolded form of `ReactionNetwork.deficiency` in
  `WantedExt/Biology/Dynamics/DeficiencyZeroWanted.lean`; the second also gives the
  deficiency with `rank Γ` in place of `s`.

The complexes, linkage graph and deficiency are taken as explicit data and hypotheses here;
this file does not define them.

## References

* M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019), §§ 3.5,
  6.4 (Theorem 6.4.7: `δ = dim (ker Y ∩ Im ∂)`).
* M. Feinberg, "Chemical reaction network structure and the stability of complex isothermal
  reactors — I", Chem. Eng. Sci. 42 (1987) 2229–2268, § 3.
-/

@[expose] public section

open Module Matrix

namespace MathlibExt.Biology.Dynamics.DeficiencyZero

variable {ρ K : Type*} [Fintype K] [DecidableEq K]

/-- **Rank of the reaction graph in complex space.** If `G` is the undirected graph on the
complexes `K` in which distinct `c`, `c'` are adjacent exactly when some reaction goes from one
to the other, then the span of the reaction vectors `e_{t r} - e_{s r}` in `ℝ^K` has dimension
`#K - ℓ`, where `ℓ` is the number of connected components (linkage classes) of `G`.

Source: Feinberg (2019), § 6.4; the Laplacian-kernel count is Mathlib's
`SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`. -/
theorem finrank_span_incidence_eq [Finite ρ] (s t : ρ → K) (G : SimpleGraph K)
    (hG : ∀ c c', G.Adj c c' ↔ c ≠ c' ∧ ∃ r, (s r = c ∧ t r = c') ∨ (s r = c' ∧ t r = c)) :
    finrank ℝ (Submodule.span ℝ
        (Set.range fun r => (Pi.single (t r) 1 - Pi.single (s r) 1 : K → ℝ))) =
      Fintype.card K - Nat.card G.ConnectedComponent := by
  classical
  have := Fintype.ofFinite ρ
  let B : Matrix K ρ ℝ := Matrix.of fun c r => (Pi.single (t r) 1 - Pi.single (s r) 1 : K → ℝ) c
  have hB : Submodule.span ℝ
      (Set.range fun r => (Pi.single (t r) 1 - Pi.single (s r) 1 : K → ℝ)) =
      Submodule.span ℝ (Set.range B.col) := rfl
  have hBt : ∀ v r, (B.transpose *ᵥ v) r = v (t r) - v (s r) := by
    intro v r
    simp [B, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
  have hker : LinearMap.ker B.transpose.mulVecLin = LinearMap.ker (G.lapMatrix ℝ).toLin' := by
    ext v
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.toLin'_apply,
      SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_adj, hG]
    constructor
    · intro h i j ⟨_, r, hr⟩
      have := congrFun h r
      rw [hBt, Pi.zero_apply, sub_eq_zero] at this
      rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact this.symm
      · exact this
    · intro h
      funext r
      rw [hBt, Pi.zero_apply, sub_eq_zero]
      by_cases hst : s r = t r
      · rw [hst]
      · exact (h (s r) (t r) ⟨hst, r, Or.inl ⟨rfl, rfl⟩⟩).symm
  have hrn := LinearMap.finrank_range_add_finrank_ker B.transpose.mulVecLin
  rw [hker, ← SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix,
    Module.finrank_fintype_fun_eq_card, ← Matrix.rank, Matrix.rank_transpose] at hrn
  rw [hB, ← Matrix.rank_eq_finrank_span_cols, Nat.card_eq_fintype_card]
  omega

end MathlibExt.Biology.Dynamics.DeficiencyZero

namespace MathlibExt.Biology.Dynamics.ComplexBalanced.ReactionNetwork

open MathlibExt.Biology.Dynamics.DeficiencyZero

variable {S ρ K : Type*} [Fintype K]

private lemma finrank_map_add_finrank_ker_inf {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] (f : V →ₗ[ℝ] W)
    (P : Submodule ℝ V) :
    finrank ℝ (P.map f) + finrank ℝ ↥(LinearMap.ker f ⊓ P) = finrank ℝ P := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict P)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have he : (LinearMap.ker f).comap P.subtype = (LinearMap.ker f ⊓ P).comap P.subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  rw [he, (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq] at h
  exact h

variable (N : ReactionNetwork S ρ)

/-- The stoichiometric subspace is the image of the complex-space reaction span
`span {e_{t r} - e_{s r}}` under the complex-composition map `Y : e_c ↦ y c`, whenever
`src r = y (s r)` and `prod r = y (t r)`.

Source: Feinberg (2019), § 6.4. -/
theorem stoichiometricSubspace_eq_map [DecidableEq K] (y : K → S → ℕ) (s t : ρ → K)
    (hs : ∀ r, N.src r = y (s r)) (ht : ∀ r, N.prod r = y (t r)) :
    N.stoichiometricSubspace =
      (Submodule.span ℝ
        (Set.range fun r => (Pi.single (t r) 1 - Pi.single (s r) 1 : K → ℝ))).map
        (Matrix.of fun i c => (y c i : ℝ)).mulVecLin := by
  rw [Submodule.map_span, ← Set.range_comp]
  unfold stoichiometricSubspace
  congr 2
  funext r i
  simp [Matrix.mulVec_sub, hs, ht]

/-- The rank of the stoichiometric matrix `Γ` (the `S × ρ` matrix whose column `r` is the
reaction vector `prod r - src r`) is the dimension of the stoichiometric subspace. -/
theorem rank_stoichiometricMatrix_eq_finrank [Fintype ρ] :
    (Matrix.of fun i r => (N.prod r i : ℝ) - N.src r i).rank =
      finrank ℝ N.stoichiometricSubspace := by
  rw [Matrix.rank_eq_finrank_span_cols]
  rfl

/-- **Deficiency as a kernel dimension.** With complexes `K`, compositions `y`, reaction
endpoints `s`, `t` and linkage graph `G` as in `finrank_span_incidence_eq`,
`s + dim (ker Y ∩ Δ) = n - ℓ`, where `s` is the dimension of the stoichiometric subspace,
`Δ = span {e_{t r} - e_{s r}}` and `Y : e_c ↦ y c`.

Source: Feinberg (2019), Theorem 6.4.7 and its proof. -/
theorem finrank_stoichiometricSubspace_add_finrank_ker_inf [DecidableEq K] [Finite ρ]
    (y : K → S → ℕ)
    (s t : ρ → K) (hs : ∀ r, N.src r = y (s r)) (ht : ∀ r, N.prod r = y (t r))
    (G : SimpleGraph K)
    (hG : ∀ c c', G.Adj c c' ↔ c ≠ c' ∧ ∃ r, (s r = c ∧ t r = c') ∨ (s r = c' ∧ t r = c)) :
    finrank ℝ N.stoichiometricSubspace +
        finrank ℝ ↥(LinearMap.ker (Matrix.of fun i c => (y c i : ℝ)).mulVecLin ⊓
          Submodule.span ℝ
            (Set.range fun r => (Pi.single (t r) 1 - Pi.single (s r) 1 : K → ℝ))) =
      Fintype.card K - Nat.card G.ConnectedComponent := by
  rw [N.stoichiometricSubspace_eq_map y s t hs ht, finrank_map_add_finrank_ker_inf,
    finrank_span_incidence_eq s t G hG]

private lemma natCard_connectedComponent_le (G : SimpleGraph K) :
    Nat.card G.ConnectedComponent ≤ Fintype.card K := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_surjective _ fun c =>
    SimpleGraph.ConnectedComponent.ind (fun v => ⟨v, rfl⟩) c

/-- **Feinberg's characterization of the deficiency.**
`n - ℓ - s = dim (ker Y ∩ Δ)`, with `n = #K`, `ℓ` the number of linkage classes, `s` the
dimension of the stoichiometric subspace, `Δ = span {e_{t r} - e_{s r}}` and `Y : e_c ↦ y c`.

Source: Feinberg (2019), Theorem 6.4.7; Feinberg (1987), § 3. -/
theorem card_sub_card_sub_finrank_eq_finrank_ker_inf [DecidableEq K] [Finite ρ]
    (y : K → S → ℕ)
    (s t : ρ → K) (hs : ∀ r, N.src r = y (s r)) (ht : ∀ r, N.prod r = y (t r))
    (G : SimpleGraph K)
    (hG : ∀ c c', G.Adj c c' ↔ c ≠ c' ∧ ∃ r, (s r = c ∧ t r = c') ∨ (s r = c' ∧ t r = c)) :
    (Fintype.card K : ℤ) - Nat.card G.ConnectedComponent -
        finrank ℝ N.stoichiometricSubspace =
      finrank ℝ ↥(LinearMap.ker (Matrix.of fun i c => (y c i : ℝ)).mulVecLin ⊓
          Submodule.span ℝ
            (Set.range fun r => (Pi.single (t r) 1 - Pi.single (s r) 1 : K → ℝ))) := by
  have h := N.finrank_stoichiometricSubspace_add_finrank_ker_inf y s t hs ht G hG
  have hle := natCard_connectedComponent_le G
  omega

/-- **The deficiency is nonnegative**: `s ≤ n - ℓ`, i.e. `0 ≤ n - ℓ - s`.

Source: Feinberg (2019), § 6.4; Feinberg (1987), § 3. -/
theorem card_sub_card_sub_finrank_nonneg [Finite ρ] (y : K → S → ℕ)
    (s t : ρ → K) (hs : ∀ r, N.src r = y (s r)) (ht : ∀ r, N.prod r = y (t r))
    (G : SimpleGraph K)
    (hG : ∀ c c', G.Adj c c' ↔ c ≠ c' ∧ ∃ r, (s r = c ∧ t r = c') ∨ (s r = c' ∧ t r = c)) :
    0 ≤ (Fintype.card K : ℤ) - Nat.card G.ConnectedComponent -
        finrank ℝ N.stoichiometricSubspace := by
  classical
  rw [N.card_sub_card_sub_finrank_eq_finrank_ker_inf y s t hs ht G hG]
  exact Int.natCast_nonneg _

/-- **Deficiency zero criterion**: `n - ℓ - s = 0` exactly when `Y` is injective on
`Δ = span {e_{t r} - e_{s r}}`, i.e. `ker Y ∩ Δ = 0`.

Source: Feinberg (2019), § 6.4. -/
theorem card_sub_card_sub_finrank_eq_zero_iff [DecidableEq K] [Finite ρ] (y : K → S → ℕ)
    (s t : ρ → K) (hs : ∀ r, N.src r = y (s r)) (ht : ∀ r, N.prod r = y (t r))
    (G : SimpleGraph K)
    (hG : ∀ c c', G.Adj c c' ↔ c ≠ c' ∧ ∃ r, (s r = c ∧ t r = c') ∨ (s r = c' ∧ t r = c)) :
    (Fintype.card K : ℤ) - Nat.card G.ConnectedComponent -
        finrank ℝ N.stoichiometricSubspace = 0 ↔
      LinearMap.ker (Matrix.of fun i c => (y c i : ℝ)).mulVecLin ⊓
          Submodule.span ℝ
            (Set.range fun r => (Pi.single (t r) 1 - Pi.single (s r) 1 : K → ℝ)) = ⊥ := by
  rw [N.card_sub_card_sub_finrank_eq_finrank_ker_inf y s t hs ht G hG, Nat.cast_eq_zero,
    Submodule.finrank_eq_zero]

/-- **Linearly independent complexes give deficiency zero.** If the complex compositions
`y c` (as vectors in `ℝ^S`) are linearly independent, then `n - ℓ - s = 0`.

Source: Feinberg (2019), § 6.4. -/
theorem card_sub_card_sub_finrank_eq_zero_of_linearIndependent [Finite ρ] (y : K → S → ℕ)
    (s t : ρ → K) (hs : ∀ r, N.src r = y (s r)) (ht : ∀ r, N.prod r = y (t r))
    (G : SimpleGraph K)
    (hG : ∀ c c', G.Adj c c' ↔ c ≠ c' ∧ ∃ r, (s r = c ∧ t r = c') ∨ (s r = c' ∧ t r = c))
    (hy : LinearIndependent ℝ fun c i => (y c i : ℝ)) :
    (Fintype.card K : ℤ) - Nat.card G.ConnectedComponent -
        finrank ℝ N.stoichiometricSubspace = 0 := by
  classical
  rw [N.card_sub_card_sub_finrank_eq_zero_iff y s t hs ht G hG]
  have hker : LinearMap.ker (Matrix.of fun i c => (y c i : ℝ)).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_eq_bot_iff]
    intro v hv
    rw [Fintype.linearIndependent_iff] at hy
    funext c
    refine hy v ?_ c
    funext i
    simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using congrFun hv i
  rw [hker, bot_inf_eq]

/-! ### The exact form: complexes `range src ∪ range prod`, linkage graph `fromRel` -/

/-- The source complex of reaction `r`, as an element of `range src ∪ range prod`. -/
private def srcC (r : ρ) : ↥(Set.range N.src ∪ Set.range N.prod) := ⟨N.src r, Or.inl ⟨r, rfl⟩⟩

/-- The product complex of reaction `r`, as an element of `range src ∪ range prod`. -/
private def prodC (r : ρ) : ↥(Set.range N.src ∪ Set.range N.prod) :=
  ⟨N.prod r, Or.inr ⟨r, rfl⟩⟩

private lemma fromRel_adj_iff (c c' : ↥(Set.range N.src ∪ Set.range N.prod)) :
    (SimpleGraph.fromRel fun a b : ↥(Set.range N.src ∪ Set.range N.prod) =>
        ∃ r, N.src r = a ∧ N.prod r = b).Adj c c' ↔
      c ≠ c' ∧ ∃ r, (N.srcC r = c ∧ N.prodC r = c') ∨ (N.srcC r = c' ∧ N.prodC r = c) := by
  simp only [SimpleGraph.fromRel_adj, srcC, prodC, Subtype.ext_iff, ← exists_or]

/-- **The deficiency is nonnegative, exact form.** For the complexes
`C = range src ∪ range prod` and the linkage graph `G = fromRel (y ⟶ y')` on `C`,
`0 ≤ #C - #(linkage classes) - dim (stoichiometric subspace)`; this is the unfolded statement
`0 ≤ N.deficiency` for `ReactionNetwork.deficiency` of
`WantedExt/Biology/Dynamics/DeficiencyZeroWanted.lean`.

Source: Feinberg (2019), § 6.4; Feinberg (1987), § 3. -/
theorem complexes_linkage_finrank_nonneg [Finite ρ] (C : Set (S → ℕ))
    (hC : C = Set.range N.src ∪ Set.range N.prod) (G : SimpleGraph C)
    (hG : G = SimpleGraph.fromRel fun c c' : C => ∃ r, N.src r = c ∧ N.prod r = c') :
    0 ≤ (Nat.card C : ℤ) - Nat.card G.ConnectedComponent -
        finrank ℝ N.stoichiometricSubspace := by
  subst hC hG
  have := Fintype.ofFinite ↥(Set.range N.src ∪ Set.range N.prod)
  rw [Nat.card_eq_fintype_card]
  exact N.card_sub_card_sub_finrank_nonneg Subtype.val N.srcC N.prodC (fun _ => rfl)
    (fun _ => rfl) _ N.fromRel_adj_iff

/-- **The deficiency in rank form, exact form.** For `C = range src ∪ range prod` and the
linkage graph `G = fromRel (y ⟶ y')`, the deficiency equals
`#C - #(linkage classes) - rank Γ`, where `Γ` is the stoichiometric matrix (column `r` is
`prod r - src r`), and this quantity is nonnegative.

Source: Feinberg (2019), § 6.4; Feinberg (1987), § 3. -/
theorem complexes_linkage_rank_nonneg [Fintype ρ] (C : Set (S → ℕ))
    (hC : C = Set.range N.src ∪ Set.range N.prod) (G : SimpleGraph C)
    (hG : G = SimpleGraph.fromRel fun c c' : C => ∃ r, N.src r = c ∧ N.prod r = c') :
    (Nat.card C : ℤ) - Nat.card G.ConnectedComponent - finrank ℝ N.stoichiometricSubspace =
        (Nat.card C : ℤ) - Nat.card G.ConnectedComponent -
          (Matrix.of fun i r => (N.prod r i : ℝ) - N.src r i).rank ∧
      0 ≤ (Nat.card C : ℤ) - Nat.card G.ConnectedComponent -
          (Matrix.of fun i r => (N.prod r i : ℝ) - N.src r i).rank := by
  rw [N.rank_stoichiometricMatrix_eq_finrank]
  exact ⟨rfl, N.complexes_linkage_finrank_nonneg C hC G hG⟩

/-- **Linearly independent complexes give deficiency zero, exact form.** If the complexes in
`C = range src ∪ range prod`, viewed as vectors in `ℝ^S`, are linearly independent, then
`#C - #(linkage classes) - dim (stoichiometric subspace) = 0` for the linkage graph
`G = fromRel (y ⟶ y')`.

Source: Feinberg (2019), § 6.4. -/
theorem complexes_linkage_finrank_eq_zero_of_linearIndependent [Finite ρ] (C : Set (S → ℕ))
    (hC : C = Set.range N.src ∪ Set.range N.prod) (G : SimpleGraph C)
    (hG : G = SimpleGraph.fromRel fun c c' : C => ∃ r, N.src r = c ∧ N.prod r = c')
    (hy : LinearIndependent ℝ fun (c : C) i => ((c : S → ℕ) i : ℝ)) :
    (Nat.card C : ℤ) - Nat.card G.ConnectedComponent -
        finrank ℝ N.stoichiometricSubspace = 0 := by
  subst hC hG
  have := Fintype.ofFinite ↥(Set.range N.src ∪ Set.range N.prod)
  rw [Nat.card_eq_fintype_card]
  exact N.card_sub_card_sub_finrank_eq_zero_of_linearIndependent Subtype.val N.srcC N.prodC
    (fun _ => rfl) (fun _ => rfl) _ N.fromRel_adj_iff hy

end MathlibExt.Biology.Dynamics.ComplexBalanced.ReactionNetwork
