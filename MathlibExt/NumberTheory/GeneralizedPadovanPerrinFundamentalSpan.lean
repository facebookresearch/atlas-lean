/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinExpansion

/-!
# The span of the Padovan–Perrin fundamental system

Every fundamental sequence solves the recurrence, and every solution is a linear combination
of the fundamental sequences with its initial values as coefficients.

## References

* Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
  *On a Model of ([k]; p; s)-Generalized Padovan–Perrin and Fibonacci Fundamental System*,
  INTEGERS 24 (2024), Article A49, pp. 4–6, Proposition 1 and Corollary 1,
  <https://math.colgate.edu/~integers/y49/y49.pdf>.
* Elen Viviani Pereira Spreafico and Mustapha Rachidi, *On generalized Pell numbers of order
  r ≥ 2*, Trends in Computational and Applied Mathematics 22 (2021), pp. 125–138,
  Proposition 2.1 (p. 128), <https://doi.org/10.5540/tcam.2021.022.01.00125>.
  Its proof uses the matching-initial-values argument credited to this work in the proof of
  Article A49's Lemma 1.
* R. Ben-Taher and Mustapha Rachidi, *On the matrix powers and exponential by the
  r-generalized Fibonacci sequences methods: the companion matrix case*, Linear Algebra and
  its Applications 370 (2003), pp. 341–353; and Bouazza El Wahbi, Mehdi Mouline, and Mustapha
  Rachidi, *Solving Nonhomogeneous Recurrence Relations of Order r by Matrix Methods*, The
  Fibonacci Quarterly 40 (2002), pp. 106–117, §2. The source credits these for the general
  Fibonacci fundamental system in §2.
-/

namespace MetaMathlibExt

variable {R : Type*}

/-- **The Fibonacci fundamental system spans the solutions.** Let $R$ be a commutative ring, let
$k_1, k_2 \in R$ and let $p, s$ be natural numbers. For $1 \le j \le s + p$ let $v^{(j)}$ be the
solution of the Padovan–Perrin recurrence with parameters $k_1, k_2, p, s$ whose initial values
are $v^{(j)}(n) = 1$ if $n + 1 = j$ and $v^{(j)}(n) = 0$ otherwise, for $n < s + p$. Then the
submodule of $R^{\mathbb{N}}$ formed by all solutions of this recurrence is the submodule spanned
by $v^{(1)}, \dots, v^{(s+p)}$.

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Corollary 1 (`integers-2024-A49-cor-1`). -/
public theorem padovanPerrin_solSpace_eq_span_fundamental [CommRing R] (k₁ k₂ : R)
    (p s : ℕ) :
    (padovanPerrinRecurrence k₁ k₂ p s).solSpace =
      Submodule.span R
        (Set.range fun j : Fin (s + p) => padovanPerrinFundamental k₁ k₂ p s ((j : ℕ) + 1)) := by
  refine le_antisymm ?_ ?_
  · intro v hv
    have hsol := (LinearRecurrence.is_sol_iff_mem_solSpace _ _).mpr hv
    have hexpand : v = ∑ j : Fin (s + p), v j • padovanPerrinFundamental k₁ k₂ p s (j + 1) := by
      funext n
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Fin.sum_univ_eq_sum_range
        (fun j => v j * padovanPerrinFundamental k₁ k₂ p s (j + 1) n)]
      exact padovanPerrin_eq_sum_fundamental k₁ k₂ p s v hsol n
    rw [hexpand]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact (LinearRecurrence.is_sol_iff_mem_solSpace _ _).mp
      (padovanPerrinFundamental_isSolution k₁ k₂ p s (j + 1))

end MetaMathlibExt
