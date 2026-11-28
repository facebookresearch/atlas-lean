# An existentially undecidable complete discretely valued field with decidable residue field

For every prime $p$ there is a complete discretely valued field of characteristic $0$ with residue characteristic $p$ whose residue field is existentially decidable and whose one-variable rational polynomials with a zero are decidable, but whose own existential theory is undecidable.

**Theorem (Dittmann).** Let $p$ be a prime number. There is a complete discretely valued field $(E, v)$ with $\mathrm{char}\,E = 0$ and residue field $Ev$ of characteristic $p$ such that

1. the existential theory of $Ev$ in the language of rings is decidable;
2. the existential theory of $E$ in the language of rings $\{+,-,\cdot,0,1\}$ is undecidable;
3. the set of polynomials in $\mathbb{Q}[X]$ with a zero in $E$ is decidable

(Theorem 1.1, Theorem 5.1). Here the existential theory of a field is the set of existential sentences $\exists \bar{x}\,\psi$ ($\psi$ quantifier-free, no parameters) of the language of rings that hold in it.

This answers a question of Anscombe and Fehm on existentially undecidable henselian fields of mixed characteristic with existentially decidable residue field and pointed value group (the value group with a constant for the value of $p$; Remark 5.3 of the source), in the strong form where even the algebraic part of $E$ is decidable.

## Depends on

- [Field](../../../../Algebra/rings-and-fields/field.md)
- [Complete theory of a first-order structure](../../../first-order-logic/theory-of-structure.md)
- [Polynomials in one variable over a semiring](../../../../Algebra/polynomials/univariate-polynomial-arithmetic/polynomial-ring.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [An existentially decidable field with an existentially undecidable quadratic extension](existentially-undecidable-quadratic-extension.md)

## Expansion

Take $K$ existentially decidable of characteristic $p$ with an existentially undecidable separable quadratic extension $L = K(\alpha)$, $a = \alpha^2 - \alpha \in K$, and with $\mathbb{F}_p$ having finite relative algebraic closure in $K$. Let $(F,v)$ be the complete discretely valued field of characteristic $0$ with residue field $K$ and uniformizer $p$, let $b \in F$ lift $a$, and set $E = F(\sqrt{p(1+4b)})$. Then $E/F$ is totally ramified, so $Ev = K$. The field $E(\sqrt{p})$ has residue field $L$, and its valuation ring and maximal ideal are existentially definable by Hensel's lemma, so $L$ is existentially interpretable in $E(\sqrt{p})$, which is quantifier-freely interpretable in $E$. Hence $E$ is existentially undecidable. Clause 3 holds because the relative algebraic closure of $\mathbb{Q}_p$ in $E$ is a finite extension of $\mathbb{Q}_p$, and local fields of characteristic $0$ have decidable theories.

## Sources

- Philip Dittmann, "Two examples concerning existential undecidability in fields", *The Journal of Symbolic Logic* 90(2):552–563, 2025, doi:10.1017/jsl.2023.87; read as arXiv:2211.01775v1, <https://arxiv.org/abs/2211.01775v1>: Theorems 1.1 and 5.1 and the proof of Theorem 5.1 of arXiv:2211.01775v1.
