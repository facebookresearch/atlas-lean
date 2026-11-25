/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.TwoCuspReductionSpan

@[expose] public section

open scoped TensorProduct MatrixGroups

/-- Source-shaped consumer: the original binders, plus the Atkin-Lehner datum `W` at `p`
that fixes the second cusp. -/
example (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (W : ModularForm.AtkinLehnerDatum M p) (K : Type*) [Field K] [Algebra (ZMod p) K] :
    Submodule.span K {x : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p W |
        ∃ (f : CuspForm (CongruenceSubgroup.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p W (⊥ : Subring ℂ)),
          x = (1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p W
            ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p W ⊥ hf⟩} = ⊤ :=
  CuspForm.span_tmul_intTwoCuspReduce_eq_top p M H W K

/-- Higher-universe consumer: the scalar field may live in `Type 1`. -/
example (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (W : ModularForm.AtkinLehnerDatum M p) (K : Type 1) [Field K] [Algebra (ZMod p) K] :
    Submodule.span K {x : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p W |
        ∃ (f : CuspForm (CongruenceSubgroup.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p W (⊥ : Subring ℂ)),
          x = (1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p W
            ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p W ⊥ hf⟩} = ⊤ :=
  CuspForm.span_tmul_intTwoCuspReduce_eq_top p M H W K

/-- Boundary: every mod-`p` form is the reduction of an element of the
two-cusp lattice. -/
example (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (W : ModularForm.AtkinLehnerDatum M p) (x : CuspForm.IntTwoCuspForms M H p W) :
    ∃ y : CuspForm.twoCuspLattice M H 2 p W (⊥ : Subring ℂ),
      CuspForm.intTwoCuspReduce M H p W y = x :=
  CuspForm.intTwoCuspReduce_surjective M H p W x

/-- Boundary: `p` annihilates the mod-`p` forms, so their exponent divides `p`.
This needs no primality of `p`: there is no `Fact p.Prime` binder here. -/
example (p : ℕ) (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (W : ModularForm.AtkinLehnerDatum M p) (x : CuspForm.IntTwoCuspForms M H p W) :
    p • x = 0 :=
  CuspForm.IntTwoCuspForms.nsmul_eq_zero M H p W x

/-- Consumer: by the span theorem the zero tensor, like every tensor, lies in
the span of the reductions. -/
example (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (W : ModularForm.AtkinLehnerDatum M p) (K : Type*) [Field K] [Algebra (ZMod p) K] :
    (0 : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p W) ∈
      Submodule.span K {x : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p W |
        ∃ (f : CuspForm (CongruenceSubgroup.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p W (⊥ : Subring ℂ)),
          x = (1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p W
            ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p W ⊥ hf⟩} := by
  rw [CuspForm.span_tmul_intTwoCuspReduce_eq_top]
  exact Submodule.mem_top

/-- A two-cusp integral form has coefficients in `A` at `∞` and at the second cusp: neither
condition sits under a quantifier over data that could be empty. -/
example (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (p : ℕ)
    (W : ModularForm.AtkinLehnerDatum M p) (A : Subring ℂ)
    (f : CuspForm (CongruenceSubgroup.GammaH M H) k)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H k p W A) (n : ℕ) :
    ModularFormClass.qCoeff (⇑f) n ∈ A ∧
      ModularFormClass.qCoeff (ModularForm.alSlash W k ⇑f) n ∈ A :=
  hf 1 (CuspForm.heckeRingH M H k).one_mem n

/-- Empty-datum boundary: when `p` does not divide `M` there is no Atkin-Lehner datum, so
the two-cusp lattice and the span theorem cannot be formed at `p` at all. -/
example (M p : ℕ) (h : ¬ p ∣ M) : IsEmpty (ModularForm.AtkinLehnerDatum M p) :=
  ⟨fun W => h ⟨W.R, W.hM⟩⟩

/-- Empty-datum boundary: `2` divides `4` but not exactly (`4 = 2 * 2` and `2` is not coprime
to `2`), so there is no datum at `M = 4`, `p = 2`. -/
example : IsEmpty (ModularForm.AtkinLehnerDatum 4 2) := by
  refine ⟨fun ⟨R, hM, a, b, hb⟩ => ?_⟩
  obtain rfl : R = 2 := by omega
  push_cast at hb
  omega

/-- A datum exists at the exact divisor `2` of `6` (`6 = 2 * 3`, `2 * 2 - 3 * 1 = 1`), and a
second one (`2 * 5 - 3 * 3 = 1`) gives the same lattice. -/
example (H : Subgroup (ZMod 6)ˣ) (k : ℤ) (A : Subring ℂ) :
    CuspForm.twoCuspLattice 6 H k 2 ⟨3, rfl, 2, 1, by norm_num⟩ A =
      CuspForm.twoCuspLattice 6 H k 2 ⟨3, rfl, 5, 3, by norm_num⟩ A :=
  CuspForm.twoCuspLattice_congr_datum 6 H k 2 _ A _
