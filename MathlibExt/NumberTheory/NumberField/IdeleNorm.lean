/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Idele
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.NumberField.ProductFormula

/-!
# Norm-one ideles

This module defines the global adelic norm (modulus) on the native
restricted-product idele group, defines its norm-one kernel, and proves
principal ideles lie in it by the number-field product formula.

ATLAS NumberTheoryI N544 / Definition 26.7. This is distinct from the
relative extension norm between idele groups.
-/

@[expose] public section

noncomputable section

namespace NumberField.TopologicalIdeleGroup

variable (K : Type*) [Field K] [NumberField K]

private theorem finite_mulSupport_norm (a : FiniteIdeleGroup (𝓞 K) K) :
    (Function.mulSupport (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      ‖(a v : v.adicCompletion K)‖)).Finite := by
  have hev := a.2
  rw [Filter.eventually_cofinite] at hev
  apply Set.Finite.subset hev
  intro v hv
  rw [Function.mem_mulSupport] at hv
  simp only [Set.mem_ofPred_eq]
  by_contra hmem
  have hvS : a v ∈ localIntegralUnitSubgroup (𝓞 K) K v := hmem
  rw [mem_localIntegralUnitSubgroup] at hvS
  obtain ⟨hint, hinv⟩ := hvS
  have h1 : ‖(a v : v.adicCompletion K)‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hint
  have h2 :
      ‖(((a v)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hinv
  have hmul : ‖(a v : v.adicCompletion K)‖ *
      ‖(((a v)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = 1 := by
    rw [← norm_mul]
    change ‖(((a v) * (a v)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = 1
    simp
  have hge : 1 ≤ ‖(a v : v.adicCompletion K)‖ := by
    by_contra hlt
    push Not at hlt
    linarith [mul_le_mul_of_nonneg_left h2
      (norm_nonneg (a v : v.adicCompletion K))]
  have heq : ‖(a v : v.adicCompletion K)‖ = 1 := le_antisymm h1 hge
  exact hv heq

/-- **Adelic norm.** Let $K$ be a number field with ring of integers $\mathcal{O}_K$. For each
infinite place $w$ of $K$ let $K_w$ be the completion of $K$ at $w$, with the absolute value
$\|\cdot\|_w$ extending $w$, and let $m_w$ be $1$ if $w$ is real and $2$ if $w$ is complex. For
each height-one prime $v$ of $\mathcal{O}_K$ let $K_v$ be the $v$-adic completion of $K$, with
the normalized absolute value $\|\cdot\|_v$. The adelic norm is the monoid homomorphism from the
topological idele group of $K$ over the Dedekind domain $\mathcal{O}_K$ to the real numbers under
multiplication that sends an idele $a$, with components $a_w \in K_w^\times$ and
$a_v \in K_v^\times$, to $\bigl(\prod_w \|a_w\|_w^{m_w}\bigr) \cdot \prod_v \|a_v\|_v$, where the
product over $v$ is the product of its finitely many factors different from $1$. -/
public noncomputable def adelicNorm : TopologicalIdeleGroup (𝓞 K) K →* ℝ :=
  show (InfiniteIdeleGroup K × FiniteIdeleGroup (𝓞 K) K) →* ℝ from
  { toFun a :=
      (∏ w : InfinitePlace K, ‖(a.1 w : w.Completion)‖ ^ w.mult) *
        ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          ‖(a.2 v : v.adicCompletion K)‖
    map_one' := by
      change
        (∏ w : InfinitePlace K, ‖(((1 : InfiniteIdeleGroup K) w : w.Completion))‖ ^ w.mult) *
        ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          ‖((((1 : FiniteIdeleGroup (𝓞 K) K) v : v.adicCompletion K)))‖ = 1
      have hinf : (∏ w : InfinitePlace K,
          ‖(((1 : InfiniteIdeleGroup K) w : w.Completion))‖ ^ w.mult) = 1 := by
        apply Finset.prod_eq_one
        intro w _
        change ‖(((1 : InfiniteIdeleGroup K) w : w.Completion))‖ ^ w.mult = 1
        change ‖((1 : (w.Completion)ˣ) : w.Completion)‖ ^ w.mult = 1
        simp
      have hfin : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          ‖((((1 : FiniteIdeleGroup (𝓞 K) K) v : v.adicCompletion K)))‖) = 1 := by
        have hfun : (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
            ‖((((1 : FiniteIdeleGroup (𝓞 K) K) v : v.adicCompletion K)))‖) =
            (fun _ => (1 : ℝ)) := by
          funext v
          change ‖((1 : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ = 1
          simp
        rw [hfun]
        exact finprod_one
      rw [hinf, hfin, mul_one]
    map_mul' := by
      intro a b
      have hinf : (∏ w : InfinitePlace K,
          ‖((((a.1 * b.1 : InfiniteIdeleGroup K) w : w.Completion)))‖ ^ w.mult) =
          (∏ w : InfinitePlace K, ‖((a.1 w : w.Completion))‖ ^ w.mult) *
            (∏ w : InfinitePlace K, ‖((b.1 w : w.Completion))‖ ^ w.mult) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro w _
        have hdef : (a.1 * b.1 : InfiniteIdeleGroup K) w = a.1 w * b.1 w := rfl
        rw [hdef, Units.val_mul, norm_mul, mul_pow]
      have hfmul : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          ‖((((a.2 * b.2 : FiniteIdeleGroup (𝓞 K) K) v : v.adicCompletion K)))‖ =
            ‖((a.2 v : v.adicCompletion K))‖ * ‖((b.2 v : v.adicCompletion K))‖ := by
        intro v
        have hdef : (a.2 * b.2 : FiniteIdeleGroup (𝓞 K) K) v = a.2 v * b.2 v := rfl
        rw [hdef, Units.val_mul, norm_mul]
      have hfin : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          ‖((((a.2 * b.2 : FiniteIdeleGroup (𝓞 K) K) v : v.adicCompletion K)))‖) =
          (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            ‖((a.2 v : v.adicCompletion K))‖) *
          (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            ‖((b.2 v : v.adicCompletion K))‖) := by
        have hfun : (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
            ‖((((a.2 * b.2 : FiniteIdeleGroup (𝓞 K) K) v : v.adicCompletion K)))‖) =
            (fun v => ‖((a.2 v : v.adicCompletion K))‖ *
              ‖((b.2 v : v.adicCompletion K))‖) := by
          funext v
          exact hfmul v
        rw [hfun]
        exact finprod_mul_distrib (finite_mulSupport_norm K a.2)
          (finite_mulSupport_norm K b.2)
      change
        (∏ w : InfinitePlace K,
          ‖(((a.1 * b.1 : InfiniteIdeleGroup K) w : w.Completion))‖ ^ w.mult) *
          ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
            ‖((((a.2 * b.2 : FiniteIdeleGroup (𝓞 K) K) v : v.adicCompletion K)))‖ =
          ((∏ w : InfinitePlace K, ‖((a.1 w : w.Completion))‖ ^ w.mult) *
            ∏ᶠ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
              ‖((a.2 v : v.adicCompletion K))‖) *
          ((∏ w : InfinitePlace K, ‖((b.1 w : w.Completion))‖ ^ w.mult) *
            ∏ᶠ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
              ‖((b.2 v : v.adicCompletion K))‖)
      rw [hinf, hfin]
      ring }

/-- **Formula for the adelic norm.** Let $K$ be a number field. For every idele $a$ of $K$ (with
$R = \mathcal{O}_K$), the adelic norm of $a$ equals
$\bigl(\prod_w \|a_w\|_w^{m_w}\bigr) \cdot \prod_v \|a_v\|_v$, where $w$ runs over the infinite
places of $K$, $\|\cdot\|_w$ is the absolute value on the completion $K_w$ extending $w$, $m_w$ is
$1$ for a real place and $2$ for a complex place, $v$ runs over the height-one primes of
$\mathcal{O}_K$, $\|\cdot\|_v$ is the normalized absolute value on the completion $K_v$, and the
product over $v$ is the product of its finitely many factors different from $1$. -/
public theorem adelicNorm_apply (a : TopologicalIdeleGroup (𝓞 K) K) :
    adelicNorm K a =
      (∏ w : InfinitePlace K, ‖(a.1 w : w.Completion)‖ ^ w.mult) *
        ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
          ‖(a.2 v : v.adicCompletion K)‖ := rfl

/-- **Norm-one ideles.** Let $K$ be a number field. The norm-one ideles of $K$ form the kernel of
the adelic norm, the subgroup of the topological idele group of $K$ (with $R = \mathcal{O}_K$)
consisting of the ideles whose adelic norm is $1$. -/
public def normOneIdeles : Subgroup (TopologicalIdeleGroup (𝓞 K) K) :=
  (adelicNorm K).ker

/-- **Membership in the norm-one ideles.** Let $K$ be a number field. An idele $a$ of $K$ (with
$R = \mathcal{O}_K$) lies in the subgroup of norm-one ideles if and only if its adelic norm
is $1$. -/
@[simp]
public theorem mem_normOneIdeles {a : TopologicalIdeleGroup (𝓞 K) K} :
    a ∈ normOneIdeles K ↔ adelicNorm K a = 1 :=
  MonoidHom.mem_ker

/-- **Product formula for principal ideles.** Let $K$ be a number field. For every
$x \in K^\times$, the principal idele of $x$ (its image under the diagonal embedding of $K^\times$
into the topological idele group, with $R = \mathcal{O}_K$) has adelic norm $1$. -/
@[simp]
public theorem adelicNorm_principalEmbedding (x : Kˣ) :
    adelicNorm K (principalEmbedding (𝓞 K) K x) = 1 := by
  rw [adelicNorm_apply, principalEmbedding_fst, principalEmbedding_snd]
  have hinf : (∏ w : NumberField.InfinitePlace K,
        ‖((infinitePrincipalEmbedding K x w : w.Completion))‖ ^ w.mult) =
      ∏ w : NumberField.InfinitePlace K, w ((x : K)) ^ w.mult := by
    apply Finset.prod_congr rfl
    intro w _
    rw [infinitePrincipalEmbedding_apply, Units.coe_map]
    change ‖algebraMap K w.Completion (x : K)‖ ^ w.mult = w (x : K) ^ w.mult
    have hco : algebraMap K w.Completion ((x : K)) =
        ((WithAbs.equiv w.1).symm ((x : K)) : w.Completion) := rfl
    rw [hco, NumberField.InfinitePlace.Completion.norm_coe]
    simp
  have hpt : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      ‖((finitePrincipalEmbedding (𝓞 K) K x v :
        v.adicCompletion K))‖ =
        (NumberField.FinitePlace.equivHeightOneSpectrum.symm v) ((x : K)) := by
    intro v
    rw [finitePrincipalEmbedding_apply, Units.coe_map]
    exact (NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply
      v ((x : K))).symm
  have hfun : (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        ‖((finitePrincipalEmbedding (𝓞 K) K x v :
          v.adicCompletion K))‖) =
      (fun v => (NumberField.FinitePlace.equivHeightOneSpectrum.symm v)
        ((x : K))) := funext hpt
  have hfin : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ‖((finitePrincipalEmbedding (𝓞 K) K x v :
          v.adicCompletion K))‖) =
      ∏ᶠ w : NumberField.FinitePlace K, w ((x : K)) := by
    rw [hfun]
    exact @finprod_comp_equiv (IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (NumberField.FinitePlace K) ℝ _
      NumberField.FinitePlace.equivHeightOneSpectrum.symm
      (f := fun w => w ((x : K)))
  rw [hinf, hfin]
  exact NumberField.prod_abs_eq_one (Units.ne_zero x)

/-- **Principal ideles have norm one.** Let $K$ be a number field. The subgroup of principal
ideles of $K$ (with $R = \mathcal{O}_K$) is contained in the subgroup of norm-one ideles; that
is, every principal idele has adelic norm $1$. -/
public theorem principalIdeles_le_normOneIdeles :
    principalIdeles (𝓞 K) K ≤ normOneIdeles K := by
  intro a ha
  obtain ⟨x, rfl⟩ := ha
  rw [mem_normOneIdeles, adelicNorm_principalEmbedding]

end NumberField.TopologicalIdeleGroup
