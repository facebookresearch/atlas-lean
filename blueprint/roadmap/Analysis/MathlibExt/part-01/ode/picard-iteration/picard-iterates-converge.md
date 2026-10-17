---
article_id: af_f54ab50a150a7fa88c24e02d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.ODE.PicardIterationWanted.picard_iterates_converge
---

# Picard iterates converge

Picard iteration converges: for a continuous right-hand side, globally
Lipschitz in the state, the Picard iterates from the constant map converge
pointwise to a global solution.

Proof: Sum the factorially bounded successive differences, obtaining locally uniform convergence
on every compact time interval. Pass the recursion through the integral and apply the fundamental
theorem of calculus. This is the argument of Teschl, Theorem 2.5 and Corollary 2.6 (Section 2.3),
for the Picard iterates (2.13) of Section 2.2, with a constant global Lipschitz constant.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.ODE.PicardIteration](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` / `Iterative methods of solving systems of real and vector-valued equations`, entry `Picard method` (unmapped); G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 2.3; stable ref https://en.wikipedia.org/wiki/Picard%E2%80%93Lindel%C3%B6f_theorem.
