# Satisfiability of existential asynchronous HyperLTL is Σ¹₁-complete

Satisfiability of asynchronous HyperLTL sentences whose trajectory quantifier is existential is Σ¹₁-complete, the same degree as satisfiability of synchronous HyperLTL.

**Theorem (Regaud and Zimmermann).** The satisfiability problem for E-AHLTL, the [asynchronous HyperLTL](asynchronous-hyperltl.md) sentences whose trajectory quantifier is $\mathsf E$, is $\Sigma^1_1$-complete (Theorem 2 of the source). For A-AHLTL, satisfiability is $\Sigma^1_1$-hard and in $\Sigma^1_2$ (Theorem 3).

## Depends on

- [Asynchronous HyperLTL](asynchronous-hyperltl.md)

## Proof depends on

- [HyperLTL satisfiability is Σ¹₁-complete](../satisfiability-of-hyperltl-and-hyperctl-star/hyperltl-satisfiability-is-sigma-1-1-complete.md)

## Expansion

*Upper bound.* Every satisfiable sentence has a countable model (Theorem 1), so satisfiability amounts to the existence of a countable set of traces, coded by a set of natural numbers, together with Skolem functions for the trace quantifiers and a trajectory, all checked by a first-order arithmetic formula; this is a $\Sigma^1_1$ condition.

*Lower bound.* HyperLTL satisfiability is $\Sigma^1_1$-hard (Fortin, Kuijer, Totzke and Zimmermann), and Bozzelli, Peron and Sánchez gave a satisfiability-preserving embedding of HyperLTL into E-AHLTL: a fresh proposition $\dagger$ is required to alternate on every trace, which by Remark 2 lets the formula restrict attention to trajectories that advance all traces at every step. For A-AHLTL the source adapts this embedding to a universal trajectory quantifier.

## Sources

- G. Regaud and M. Zimmermann, "The Complexity of Asynchronous HyperLTL", *Electronic Proceedings in Theoretical Computer Science* 454, 2026, pp. 183–199, <https://doi.org/10.4204/EPTCS.454.13>; read as arXiv:2606.06091v2, <https://arxiv.org/abs/2606.06091v2>: Theorems 1, 2 and 3 with their proofs (Section 3) and Remark 2.
