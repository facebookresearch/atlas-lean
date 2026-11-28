/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Module.ZLattice.FirstAndLastMinimum
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The last minimum of an orthogonal direct sum of lattices

For lattices `L₁ ⊆ E₁` and `L₂ ⊆ E₂` in Euclidean spaces, the lattice `L₁ ⊕ L₂` of the
orthogonal direct sum `WithLp 2 (E₁ × E₂)` has last minimum
`Λ(L₁ ⊕ L₂) = max(Λ(L₁), Λ(L₂))`, as Gaudron and Rémond use in *Polarisations et isogénies*,
p. 2070 and in the proof of their Lemme 9.2, p. 2099.

* `ZLattice.lastMinimum_eq_sInf_span`: the last minimum is the infimum of the `r > 0` for which
  the vectors of `L` of norm at most `r` span `E`;
* `ZLattice.prodL2`: the lattice `L₁ ⊕ L₂` of `WithLp 2 (E₁ × E₂)`;
* `ZLattice.lastMinimum_prodL2`: `Λ(L₁ ⊕ L₂) = max(Λ(L₁), Λ(L₂))`.
-/

@[expose] public section

open Module

namespace ZLattice

section span

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A $\mathbb{Z}$-submodule $L$ of a real inner product space $E$ of dimension $n$ contains $n$
linearly independent vectors of norm at most $r$ if and only if the vectors of $L$ of norm at most
$r$ span $E$ over $\mathbb{R}$. -/
theorem exists_linearIndependent_norm_le_iff_span_eq_top (L : Submodule ℤ E) (r : ℝ) :
    (∃ ω : Fin (finrank ℝ E) → E, LinearIndependent ℝ ω ∧ ∀ i, ω i ∈ L ∧ ‖ω i‖ ≤ r) ↔
      Submodule.span ℝ {x : E | x ∈ L ∧ ‖x‖ ≤ r} = ⊤ := by
  constructor
  · rintro ⟨ω, hω, hωL⟩
    have hcard := linearIndependent_iff_card_eq_finrank_span.mp hω
    rw [Fintype.card_fin, Set.finrank] at hcard
    have htop : Submodule.span ℝ (Set.range ω) = ⊤ := Submodule.eq_top_of_finrank_eq hcard.symm
    rw [eq_top_iff, ← htop]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact hωL i
  · intro hspan
    obtain ⟨b, hbS, hbspan, hli⟩ := exists_linearIndependent ℝ {x : E | x ∈ L ∧ ‖x‖ ≤ r}
    let B : Basis b ℝ E := Basis.mk hli (by rw [Subtype.range_coe, hbspan, hspan])
    have : Finite b := Module.Finite.finite_basis B
    have : Fintype b := Fintype.ofFinite b
    let e : Fin (finrank ℝ E) ≃ b := (Fintype.equivFinOfCardEq (finrank_eq_card_basis B).symm).symm
    refine ⟨fun i ↦ (e i : E), hli.comp e e.injective, fun i ↦ hbS (e i).2⟩

/-- **The last minimum through spanning sets.** For a $\mathbb{Z}$-submodule $L$ of a
finite-dimensional real inner product space $E$, the last minimum $\Lambda(L)$ is the infimum of
the real numbers $r > 0$ such that the vectors of $L$ of norm at most $r$ span $E$:
$$\Lambda(L) = \inf\{r > 0 : \operatorname{span}_{\mathbb{R}}\{x \in L : |x| \le r\} = E\}.$$

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, §3, p. 2069 (the definition of $\Lambda$ through free families). -/
theorem lastMinimum_eq_sInf_span (L : Submodule ℤ E) :
    lastMinimum L = sInf {r : ℝ | 0 < r ∧ Submodule.span ℝ {x : E | x ∈ L ∧ ‖x‖ ≤ r} = ⊤} := by
  unfold lastMinimum
  congr 1
  ext r
  exact and_congr_right fun _ ↦ exists_linearIndependent_norm_le_iff_span_eq_top L r

omit [FiniteDimensional ℝ E] in
/-- The set of the `r > 0` for which the vectors of `L` of norm at most `r` span `E` is closed
upwards. -/
theorem span_norm_le_eq_top_mono {L : Submodule ℤ E} {r r' : ℝ} (hrr' : r ≤ r')
    (hr : Submodule.span ℝ {x : E | x ∈ L ∧ ‖x‖ ≤ r} = ⊤) :
    Submodule.span ℝ {x : E | x ∈ L ∧ ‖x‖ ≤ r'} = ⊤ := by
  rw [eq_top_iff, ← hr]
  exact Submodule.span_mono fun x hx ↦ ⟨hx.1, hx.2.trans hrr'⟩

/-- For a lattice $L$ in $E$, some $r > 0$ has the vectors of $L$ of norm at most $r$ spanning
$E$. -/
theorem exists_span_norm_le_eq_top (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ r : ℝ, 0 < r ∧ Submodule.span ℝ {x : E | x ∈ L ∧ ‖x‖ ≤ r} = ⊤ := by
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ L) = finrank ℝ E := by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  set B := ((Free.chooseBasis ℤ L).reindex (Fintype.equivFinOfCardEq hcard)).ofZLatticeBasis ℝ L
  refine ⟨1 + ∑ i, ‖B i‖,
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ ↦ norm_nonneg _),
    (exists_linearIndependent_norm_le_iff_span_eq_top L _).mp ⟨B, B.linearIndependent,
      fun i ↦ ⟨?_, ?_⟩⟩⟩
  · rw [Module.Basis.ofZLatticeBasis_apply]
    exact Subtype.mem _
  · have := Finset.single_le_sum (f := fun i ↦ ‖B i‖) (fun i _ ↦ norm_nonneg _)
      (Finset.mem_univ i)
    linarith

end span

/-- For two nonempty sets of real numbers that are bounded below and closed upwards, the infimum
of their intersection is the larger of their infima. -/
theorem _root_.Real.sInf_inter_of_upwardClosed {s t : Set ℝ} (hs : s.Nonempty) (ht : t.Nonempty)
    (hsb : BddBelow s) (htb : BddBelow t) (hsu : ∀ a ∈ s, ∀ b, a ≤ b → b ∈ s)
    (htu : ∀ a ∈ t, ∀ b, a ≤ b → b ∈ t) :
    sInf (s ∩ t) = max (sInf s) (sInf t) := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  have hne : (s ∩ t).Nonempty :=
    ⟨max a b, hsu a ha _ (le_max_left a b), htu b hb _ (le_max_right a b)⟩
  apply le_antisymm
  · refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    obtain ⟨a', ha's, ha'⟩ := exists_lt_of_csInf_lt ⟨a, ha⟩ (lt_add_of_pos_right (sInf s) hε)
    obtain ⟨b', hb't, hb'⟩ := exists_lt_of_csInf_lt ⟨b, hb⟩ (lt_add_of_pos_right (sInf t) hε)
    have hmem : max a' b' ∈ s ∩ t :=
      ⟨hsu a' ha's _ (le_max_left a' b'), htu b' hb't _ (le_max_right a' b')⟩
    refine (csInf_le (hsb.mono Set.inter_subset_left) hmem).trans_lt ?_
    rw [max_lt_iff]
    exact ⟨ha'.trans_le (by gcongr; exact le_max_left _ _),
      hb'.trans_le (by gcongr; exact le_max_right _ _)⟩
  · exact max_le (csInf_le_csInf hsb hne Set.inter_subset_left)
      (csInf_le_csInf htb hne Set.inter_subset_right)

section prod

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]

/-- The lattice $L_1 \oplus L_2$ of the orthogonal direct sum `WithLp 2 (E₁ × E₂)` of two real
inner product spaces, for $\mathbb{Z}$-submodules $L_1 \subseteq E_1$ and $L_2 \subseteq E_2$: the
vectors $x$ with first component in $L_1$ and second component in $L_2$. -/
noncomputable def prodL2 (L₁ : Submodule ℤ E₁) (L₂ : Submodule ℤ E₂) :
    Submodule ℤ (WithLp 2 (E₁ × E₂)) :=
  (L₁.prod L₂).comap (WithLp.linearEquiv 2 ℤ (E₁ × E₂)).toLinearMap

omit [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁] [InnerProductSpace ℝ E₂]
  [FiniteDimensional ℝ E₂] in
theorem mem_prodL2 {L₁ : Submodule ℤ E₁} {L₂ : Submodule ℤ E₂} {x : WithLp 2 (E₁ × E₂)} :
    x ∈ prodL2 L₁ L₂ ↔ x.fst ∈ L₁ ∧ x.snd ∈ L₂ :=
  Iff.rfl

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] in
/-- The vectors of norm at most $r$ of $L_1 \oplus L_2$ span `WithLp 2 (E₁ × E₂)` if and only if
those of $L_1$ span $E_1$ and those of $L_2$ span $E_2$. -/
theorem span_norm_le_prodL2_eq_top_iff (L₁ : Submodule ℤ E₁) (L₂ : Submodule ℤ E₂) (r : ℝ) :
    Submodule.span ℝ {x : WithLp 2 (E₁ × E₂) | x ∈ prodL2 L₁ L₂ ∧ ‖x‖ ≤ r} = ⊤ ↔
      Submodule.span ℝ {x : E₁ | x ∈ L₁ ∧ ‖x‖ ≤ r} = ⊤ ∧
        Submodule.span ℝ {x : E₂ | x ∈ L₂ ∧ ‖x‖ ≤ r} = ⊤ := by
  set e := (WithLp.linearEquiv 2 ℝ (E₁ × E₂)).toLinearMap
  set p₁ : WithLp 2 (E₁ × E₂) →ₗ[ℝ] E₁ := LinearMap.fst ℝ E₁ E₂ ∘ₗ e
  set p₂ : WithLp 2 (E₁ × E₂) →ₗ[ℝ] E₂ := LinearMap.snd ℝ E₁ E₂ ∘ₗ e
  set i₁ : E₁ →ₗ[ℝ] WithLp 2 (E₁ × E₂) :=
    (WithLp.linearEquiv 2 ℝ (E₁ × E₂)).symm.toLinearMap ∘ₗ LinearMap.inl ℝ E₁ E₂
  set i₂ : E₂ →ₗ[ℝ] WithLp 2 (E₁ × E₂) :=
    (WithLp.linearEquiv 2 ℝ (E₁ × E₂)).symm.toLinearMap ∘ₗ LinearMap.inr ℝ E₁ E₂
  have hfst : ∀ x : WithLp 2 (E₁ × E₂), ‖x.fst‖ ≤ ‖x‖ := fun x ↦ by
    rw [WithLp.prod_norm_eq_of_L2]
    exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))
  have hsnd : ∀ x : WithLp 2 (E₁ × E₂), ‖x.snd‖ ≤ ‖x‖ := fun x ↦ by
    rw [WithLp.prod_norm_eq_of_L2]
    exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg _))
  constructor
  · intro h
    have hp₁ : Function.Surjective p₁ := fun y ↦ ⟨WithLp.toLp 2 (y, 0), rfl⟩
    have hp₂ : Function.Surjective p₂ := fun y ↦ ⟨WithLp.toLp 2 (0, y), rfl⟩
    constructor
    · rw [eq_top_iff, ← LinearMap.range_eq_top.mpr hp₁, LinearMap.range_eq_map, ← h,
        Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(mem_prodL2.mp hx.1).1, (hfst x).trans hx.2⟩
    · rw [eq_top_iff, ← LinearMap.range_eq_top.mpr hp₂, LinearMap.range_eq_map, ← h,
        Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(mem_prodL2.mp hx.1).2, (hsnd x).trans hx.2⟩
  · rintro ⟨h₁, h₂⟩
    set S := Submodule.span ℝ {x : WithLp 2 (E₁ × E₂) | x ∈ prodL2 L₁ L₂ ∧ ‖x‖ ≤ r}
    have hi₁ : ∀ y : E₁, i₁ y ∈ S := by
      intro y
      have hy : y ∈ Submodule.span ℝ {x : E₁ | x ∈ L₁ ∧ ‖x‖ ≤ r} := h₁ ▸ Submodule.mem_top
      have hmap : Submodule.map i₁ (Submodule.span ℝ {x : E₁ | x ∈ L₁ ∧ ‖x‖ ≤ r}) ≤ S := by
        rw [Submodule.map_span]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, hx, rfl⟩
        refine ⟨mem_prodL2.mpr ⟨hx.1, zero_mem L₂⟩, ?_⟩
        rw [WithLp.prod_norm_eq_of_L2]
        simpa [i₁, Real.sqrt_sq (norm_nonneg x)] using hx.2
      exact hmap (Submodule.mem_map_of_mem hy)
    have hi₂ : ∀ y : E₂, i₂ y ∈ S := by
      intro y
      have hy : y ∈ Submodule.span ℝ {x : E₂ | x ∈ L₂ ∧ ‖x‖ ≤ r} := h₂ ▸ Submodule.mem_top
      have hmap : Submodule.map i₂ (Submodule.span ℝ {x : E₂ | x ∈ L₂ ∧ ‖x‖ ≤ r}) ≤ S := by
        rw [Submodule.map_span]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, hx, rfl⟩
        refine ⟨mem_prodL2.mpr ⟨zero_mem L₁, hx.1⟩, ?_⟩
        rw [WithLp.prod_norm_eq_of_L2]
        simpa [i₂, Real.sqrt_sq (norm_nonneg x)] using hx.2
      exact hmap (Submodule.mem_map_of_mem hy)
    rw [eq_top_iff]
    intro v _
    have hv : v = i₁ v.fst + i₂ v.snd := by
      apply WithLp.ofLp_injective
      ext <;> simp [i₁, i₂]
    rw [hv]
    exact S.add_mem (hi₁ _) (hi₂ _)

/-- **The last minimum of an orthogonal direct sum of lattices.** Let $E = E_1 \oplus E_2$ be the
orthogonal direct sum `WithLp 2 (E₁ × E₂)` of two finite-dimensional real inner product spaces and
$\Gamma_1 \subset E_1$, $\Gamma_2 \subset E_2$ lattices, so that $\Gamma = \Gamma_1 \oplus \Gamma_2$
(`ZLattice.prodL2`) is a lattice of $E$. Then, for the last minima,
$$\Lambda(\Gamma_1 \oplus \Gamma_2) = \max\bigl(\Lambda(\Gamma_1), \Lambda(\Gamma_2)\bigr).$$
The dimensions of $E_1$ and $E_2$ may be $0$.

The proof shows that the vectors of norm at most $r$ of $\Gamma$ span $E$ exactly when those of
$\Gamma_1$ and $\Gamma_2$ span $E_1$ and $E_2$: one direction projects to $E_1$ and $E_2$, the
other includes $E_1$ and $E_2$ into $E$.

Source: É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014),
2057–2108, p. 2070 (an orthogonal decomposition gives
$\Lambda(\operatorname{Hom}_K(A \times B, C)) = \max(\Lambda(\operatorname{Hom}_K(A, C)),
\Lambda(\operatorname{Hom}_K(B, C)))$), and the proof of Lemme 9.2, p. 2099. -/
theorem lastMinimum_prodL2 (L₁ : Submodule ℤ E₁) (L₂ : Submodule ℤ E₂) [DiscreteTopology L₁]
    [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂] :
    lastMinimum (prodL2 L₁ L₂) = max (lastMinimum L₁) (lastMinimum L₂) := by
  rw [lastMinimum_eq_sInf_span, lastMinimum_eq_sInf_span, lastMinimum_eq_sInf_span]
  have hset : {r : ℝ | 0 < r ∧ Submodule.span ℝ
      {x : WithLp 2 (E₁ × E₂) | x ∈ prodL2 L₁ L₂ ∧ ‖x‖ ≤ r} = ⊤} =
      {r : ℝ | 0 < r ∧ Submodule.span ℝ {x : E₁ | x ∈ L₁ ∧ ‖x‖ ≤ r} = ⊤} ∩
        {r : ℝ | 0 < r ∧ Submodule.span ℝ {x : E₂ | x ∈ L₂ ∧ ‖x‖ ≤ r} = ⊤} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, span_norm_le_prodL2_eq_top_iff]
    tauto
  rw [hset]
  refine Real.sInf_inter_of_upwardClosed (exists_span_norm_le_eq_top L₁)
    (exists_span_norm_le_eq_top L₂) ⟨0, fun r hr ↦ hr.1.le⟩ ⟨0, fun r hr ↦ hr.1.le⟩ ?_ ?_
  · exact fun a ha b hab ↦ ⟨ha.1.trans_le hab, span_norm_le_eq_top_mono hab ha.2⟩
  · exact fun a ha b hab ↦ ⟨ha.1.trans_le hab, span_norm_le_eq_top_mono hab ha.2⟩

end prod

end ZLattice
