/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import MathlibExt.AlgebraicGeometry.AlgebraicallyClosedPadicTests
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.OrderClosed

/-!
# `p`-adic completeness of the valuation ring

The ring `O_C` of norm-at-most-one elements of an algebraically closed
complete nonarchimedean extension `C` of `Q_p` is `p`-adically complete
and separated (`integers_adic_complete`).

Source: Scholze--Weinstein, arXiv:1211.6357v2, Sections 1--3 and 5.1;
Messing, The crystals associated to Barsotti--Tate groups, Chapter II.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.PDivisibleHodgeTateRealization

open Filter
open scoped Topology
open MathlibExt.AlgebraicGeometry.AlgebraicallyClosedPadicTests

/-- The norm of `p` in `C` is the inverse of `p`, through `Q_p`. -/
private theorem norm_p_field (p : ℕ) [Fact p.Prime] (C : FieldTest p) :
    ‖(p : C.field)‖ = (p : ℝ)⁻¹ := by
  have h1 : (p : C.field) = algebraMap (Padic p) C.field (p : Padic p) := by simp
  rw [h1, C.norm_coefficients, Padic.norm_p]

/-- `p` is nonzero in `C`, since its norm is nonzero. -/
private theorem p_ne_zero_field (p : ℕ) [Fact p.Prime] (C : FieldTest p) :
    (p : C.field) ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_p_field p C]
  exact inv_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- Membership in `(p^n)` is a norm bound. -/
private theorem mem_span_pow_iff (p : ℕ) [Fact p.Prime] (C : FieldTest p)
    (x : integers p C) (n : ℕ) :
    x ∈ Ideal.span ({((p : integers p C) ^ n)} : Set (integers p C)) ↔
      ‖(x : C.field)‖ ≤ ‖(p : C.field) ^ n‖ := by
  constructor
  · intro hx
    rw [Ideal.mem_span_singleton] at hx
    obtain ⟨y, hy⟩ := hx
    have hyC : (x : C.field) = (p : C.field) ^ n * (y : C.field) := by
      have hcongr := congrArg (fun z : integers p C => (z : C.field)) hy
      simpa using hcongr
    rw [hyC, norm_mul]
    calc ‖(p : C.field) ^ n‖ * ‖(y : C.field)‖
        ≤ ‖(p : C.field) ^ n‖ * 1 :=
          mul_le_mul_of_nonneg_left y.property (norm_nonneg _)
      _ = ‖(p : C.field) ^ n‖ := mul_one _
  · intro hle
    rw [Ideal.mem_span_singleton]
    have hpn : (p : C.field) ^ n ≠ 0 := pow_ne_zero n (p_ne_zero_field p C)
    have hpos : 0 < ‖(p : C.field) ^ n‖ := norm_pos_iff.mpr hpn
    have hy : ‖(x : C.field) / (p : C.field) ^ n‖ ≤ 1 := by
      rw [norm_div]
      exact (div_le_one hpos).mpr hle
    refine ⟨⟨(x : C.field) / (p : C.field) ^ n, hy⟩, ?_⟩
    apply Subtype.ext
    have hmul : ((((p : integers p C) ^ n *
        ⟨(x : C.field) / (p : C.field) ^ n, hy⟩ : integers p C)) : C.field) =
        (p : C.field) ^ n * ((x : C.field) / (p : C.field) ^ n) := by simp
    rw [hmul]
    exact (mul_div_cancel₀ _ hpn).symm

/-- The `n`-th adic neighborhood of `0` is a norm ball. -/
private theorem smodEq_zero_iff_norm (p : ℕ) [Fact p.Prime] (C : FieldTest p)
    (x : integers p C) (n : ℕ) :
    x ≡ 0 [SMOD ((Ideal.span {(p : integers p C)}) ^ n • ⊤ :
      Submodule (integers p C) (integers p C))] ↔
      ‖(x : C.field)‖ ≤ ‖(p : C.field) ^ n‖ := by
  simp only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, SModEq.zero]
  exact mem_span_pow_iff p C x n

/-- The `n`-th adic neighborhood is a norm ball. -/
private theorem smodEq_iff_norm (p : ℕ) [Fact p.Prime] (C : FieldTest p)
    (x y : integers p C) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {(p : integers p C)}) ^ n • ⊤ :
      Submodule (integers p C) (integers p C))] ↔
      ‖(x : C.field) - (y : C.field)‖ ≤ ‖(p : C.field) ^ n‖ := by
  simp only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, SModEq.sub_mem]
  have h := mem_span_pow_iff p C (x - y) n
  have hcast : ((x - y : integers p C) : C.field) =
      (x : C.field) - (y : C.field) := by simp
  rw [hcast] at h
  exact h

/-- Powers of `‖p‖` tend to zero. -/
private theorem tendsto_inv_pow (p : ℕ) [Fact p.Prime] :
    Tendsto (fun n : ℕ => ((p : ℝ)⁻¹) ^ n) atTop (𝓝 0) := by
  apply tendsto_pow_atTop_nhds_zero_of_lt_one
  · exact inv_nonneg.mpr (Nat.cast_nonneg p)
  · apply inv_lt_one_of_one_lt₀
    exact_mod_cast (Fact.out : p.Prime).one_lt

/-- Hausdorff: an element in every `(p^n)` is zero. -/
private theorem haus_field (p : ℕ) [Fact p.Prime] (C : FieldTest p) :
    IsHausdorff (Ideal.span {(p : integers p C)}) (integers p C) := by
  rw [isHausdorff_iff]
  intro x hx
  have hbound : ∀ n : ℕ, ‖(x : C.field)‖ ≤ ((p : ℝ)⁻¹) ^ n := fun n => by
    have h1 := (smodEq_zero_iff_norm p C x n).mp (hx n)
    rwa [norm_pow, norm_p_field p C] at h1
  have h0 : ‖(x : C.field)‖ ≤ 0 :=
    ge_of_tendsto (tendsto_inv_pow p) (Eventually.of_forall hbound)
  rw [norm_le_zero_iff] at h0
  apply Subtype.ext
  simpa using h0

/-- Precomplete: every adic Cauchy sequence converges. -/
private theorem prec_field (p : ℕ) [Fact p.Prime] (C : FieldTest p) :
    IsPrecomplete (Ideal.span {(p : integers p C)}) (integers p C) := by
  rw [isPrecomplete_iff]
  intro f hf
  have hbound : ∀ m n : ℕ, m ≤ n →
      dist ((f m : integers p C) : C.field) ((f n : integers p C) : C.field) ≤
        ((p : ℝ)⁻¹) ^ m := by
    intro m n hmn
    have h1 := (smodEq_iff_norm p C (f m) (f n) m).mp (hf hmn)
    rw [dist_eq_norm]
    rwa [norm_pow, norm_p_field p C] at h1
  have hc : CauchySeq (fun n : ℕ => ((f n : integers p C) : C.field)) :=
    cauchySeq_of_le_tendsto_0' _ hbound (tendsto_inv_pow p)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  have hL1 : ‖L‖ ≤ 1 := by
    refine le_of_tendsto hL.norm (Eventually.of_forall fun n => (f n).property)
  refine ⟨⟨L, hL1⟩, fun n => ?_⟩
  rw [smodEq_iff_norm]
  have hseq : Tendsto
      (fun m : ℕ => ‖((f n : integers p C) : C.field) - ((f m : integers p C) : C.field)‖)
      atTop (𝓝 ‖((f n : integers p C) : C.field) - L‖) :=
    (tendsto_const_nhds.sub hL).norm
  refine le_of_tendsto hseq ?_
  rw [eventually_atTop]
  refine ⟨n, fun m hm => ?_⟩
  exact (smodEq_iff_norm p C (f n) (f m) n).mp (hf hm)

/-- $p$-adic completeness of the ring of integers: let $p$ be a prime and $C$ an algebraically
closed complete non-archimedean normed field extension of $\mathbb{Q}_p$ whose norm extends that of
$\mathbb{Q}_p$. Then $\mathcal{O}_C$, the elements of norm at most $1$, is $p$-adically complete and
separated. -/
public theorem integers_adic_complete
    (p : ℕ) [Fact p.Prime] (C : FieldTest p) :
    IsAdicComplete (Ideal.span {(p : integers p C)}) (integers p C) where
  haus' := (haus_field p C).haus'
  prec' := (prec_field p C).prec'

end WantedExt.AlgebraicGeometry.PDivisibleHodgeTateRealization
