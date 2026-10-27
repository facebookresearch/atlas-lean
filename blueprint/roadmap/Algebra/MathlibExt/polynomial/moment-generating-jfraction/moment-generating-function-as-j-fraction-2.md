---
article_id: af_4d168860facf2ac3df05e42f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.moment_generating_function_as_J_fraction
---

# Moment generating function as J fraction

Moment generating function as J-fraction for monic orthogonal polynomials:
Favard three-term recurrence implies the moment power series equals the
coefficientwise infinite J-fraction limit.

The source's recurrence line reads `beta_n(x)`; it is rendered as
`beta_n p_{n-1}` per the surrounding lines 315–317 and 364–366.
It follows from `moment_generating_function_as_J_fraction_general`; the monicity and degree,
`β n ≠ 0`, nonzero-norm and `μ 0 ≠ 0` hypotheses are unused and keep the source's shape, and
orthogonality is used only to get `L (p n) = 0` for `n ≥ 1`.
Proves `Wanted` entry `moment_generating_function_as_J_fraction`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Has Jacobi Fraction](../../../../NumberTheory/MathlibExt/part-06/hankel-transform/has-jacobi-fraction.md)
- [Moment generating function as J fraction general](moment-generating-function-as-j-fraction.md)

## Sources

- [MathlibExt, MathlibExt.Algebra.Polynomial.MomentGeneratingJFraction](../../../../../sources/v2/MathlibExt.md)
- Paul Barry and Aoife Hennessy, "Meixner-Type Results for Riordan Arrays and Associated Integer Sequences," Journal of Integer Sequences 13 (2010), Article 10.9.4, J-fraction theorem citing C. Krattenthaler (cf. Viennot Proposition 1, (7), p. V-5; Wall Theorem 51.1), lines 353–362, https://cs.uwaterloo.ca/journals/JIS/VOL13/Barry5/barry96s.tex
