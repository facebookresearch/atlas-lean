# Semantics preservation of floating-point compilation

This node collects which compiler transformations preserve floating-point semantics, in a model where each
operation is a single IEEE operation with a fixed rounding mode.

## Expansion

A sound expansion has separate pages for:

1. **Observation model.** Results are compared bit for bit, including NaN payloads only when the payload semantics is
   fixed, or modulo NaN equivalence (all NaNs identified).
2. **Sound transformations.** Correctly rounded constant folding under the same operation and NaN conventions;
   commuting the operands of $+$ and $\times$ in a canonical-NaN model or modulo NaN equivalence.
3. **Unsound transformations,** each with an explicit counterexample: reassociation, contraction of a multiply and an
   add into a fused multiply-add, and evaluation in extended precision followed by rounding.
4. **Compiler correctness,** as a source-qualified page: the floating-point part of a verified compiler's correctness
   theorem, with its source language, observations and NaN hypotheses taken from the primary source.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Structural operational semantics.

## Depends on

- [Total IEEE-style operation semantics with special values and exceptions](total-ieee-style-operation-semantics-with-special-values-and.md)

## Sources

- Verified Compilation of Floating-Point Computations — S. Boldo, J.-H. Jourdan, X. Leroy, G. Melquiond, Journal of Automated Reasoning, Sec. 1 (Fast-Two-Sum example, double rounding, contraction to FMA), Sec. 3.2, Theorem 1 in Sec. 4, and Sec. 6.1-6.2 (compile-time evaluation, algebraic simplifications and their NaN payload hypotheses). <https://xavierleroy.org/publi/floating-point-compcert.pdf>
- What Every Computer Scientist Should Know About Floating-Point Arithmetic — D. Goldberg, ACM Computing Surveys 23(1), 1991, Sec. 3.2.3 Optimizers (constant folding, common subexpressions, x = x and NaN). <https://www.cs.tufts.edu/comp/40/docs/WhatEveryComputerScientistShouldKnowAboutFloatingPointArithmetic.pdf>
