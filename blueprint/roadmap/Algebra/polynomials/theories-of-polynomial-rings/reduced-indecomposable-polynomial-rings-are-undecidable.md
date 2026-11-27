# Polynomial rings over reduced indecomposable rings have undecidable theories

If a commutative ring R has no nonzero nilpotents and no idempotents other than 0 and 1, the first-order theory of the polynomial ring R[x] in the language of rings is undecidable, and one formula defines the prime subring in all such rings.

Let $R$ be a commutative ring with identity. $R$ is *reduced* if its only nilpotent element is $0$, and *indecomposable* if its only idempotents are $0$ and $1$; integral domains are reduced and indecomposable, and the class is strictly larger (for example $\mathbb{Q}[s, t]/(st)$). Let $S = R[x]$ be the polynomial ring in one variable over $R$, viewed as a structure for the language $(0, 1, +, \cdot)$ of rings, and let $\mathbb{Z}^+_S = \{n \cdot 1 : n \ge 1\}$ be the set of positive integer multiples of $1$ in $S$, which generates the *prime subring* $\mathbb{Z}_S$, the smallest subring of $S$.

**Theorem (Barone–Caro–Naziazeno).** Let $R$ be a reduced indecomposable commutative ring with identity and $S = R[x]$.

1. The theory $\operatorname{Th}(S)$, the set of sentences of the language of rings true in $S$, is undecidable.
2. There is a single formula $\Omega(t)$ of the language of rings, not depending on $R$, that defines $\mathbb{Z}^+_S$ in $S$; hence the prime subring of $S$ is definable, uniformly over all such $R$.

Conventions: no parameters from $S$ are allowed in sentences or in $\Omega$; clause 1 holds in every characteristic. Clause 1 extends Raphael Robinson's undecidability of polynomial rings over integral domains.

## Depends on

- [Commutative ring with identity](../../rings-and-fields/commutative-ring-with-identity.md)
- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)
- [Predicates decidable by a single-tape Turing machine](../../../TheoryOfComputation/turing-machines/single-tape/decidable-and-recognizable-predicates-on-single/single-tape-decidable.md)

## Proof depends on

None.

## Expansion

For clause 1 the source extends a method of Raphael Robinson. It defines, by first-order formulas, a nonempty set $V$ of regular non-invertible elements $p$ of $S$ for which the set $\{1\} \cup \{p^k : k \ge 1\}$ of nonnegative powers is defined by a formula $\beta(t, p)$ (the *logical powers* of $p$). Each sentence $\varphi$ about the semiring $(\mathbb{N}, +, \cdot, 0, 1)$ translates, with $p^k$ standing for $k$, into a formula $\varphi_\beta(p)$, and $\varphi$ is true in $\mathbb{N}$ exactly when $\forall p\, (p \in V \to \varphi_\beta(p))$ holds in $S$; this translation is computable, so a decision procedure for $\operatorname{Th}(S)$ would decide $\operatorname{Th}(\mathbb{N}, +, \cdot, 0, 1)$, which is undecidable. For clause 2 the source gives two formulas defining $\mathbb{Z}^+_S$, one when every nonzero integer is invertible in $S$ and one when $R$ is a nonfield of characteristic zero, and a sentence $\Xi$ that distinguishes the cases, combined into $\Omega(t) = (\neg \Xi \wedge \Theta(t)) \vee (\Xi \wedge \Upsilon(t))$. In characteristic zero clause 2 interprets the ring $\mathbb{Z}$ with its operations inside $S$, which gives undecidability a second way.

A good expansion adds and links pages for the undecidability of the first-order theory of $(\mathbb{N}, +, \cdot, 0, 1)$ and for the definability of logical powers in reduced indecomposable polynomial rings.

## Sources

- Marco Barone, Nicolás Caro-Montoya and Eudes Naziazeno, *Uniform definability of integers in reduced indecomposable polynomial rings*, The Journal of Symbolic Logic 85 (2020), no. 4, 1376–1402, https://doi.org/10.1017/jsl.2020.50; read as arXiv:1703.08266v7, where clause 1 is Theorem 6.1 and clause 2 is Theorem 6.11, with the definitions in Section 2 and the example $\mathbb{Q}[s, t]/(st)$ in Section 4.2 and Section 6.5.
- Raphael M. Robinson, *Undecidable rings*, Transactions of the American Mathematical Society 70 (1951), 137–159, https://doi.org/10.2307/1990529, for the integral-domain case, as cited in the paper above.
