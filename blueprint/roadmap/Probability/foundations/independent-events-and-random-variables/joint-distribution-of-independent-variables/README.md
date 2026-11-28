# Joint distribution of independent random variables

Let $\mu$ be a measure on $\Omega$, and let $f_i \colon \Omega \to \beta_i$, for $i$ in a finite index set $\iota$, be
almost everywhere measurable maps into measurable spaces. If the family $(f_i)$ is independent with respect to $\mu$,
then the image of $\mu$ under $\omega \mapsto (f_i(\omega))_{i \in \iota}$ is the product of the laws $\mu \circ f_i^{-1}$ on
$\prod_i \beta_i$.

## Idea

For independent real random variables $X_1, \dots, X_n$ with laws $\mu_1, \dots, \mu_n$, the random vector
$(X_1, \dots, X_n)$ has law $\mu_1 \times \cdots \times \mu_n$ on $\mathbb R^n$. So independence is a property of the joint
law: it holds exactly when the joint law is the product of the individual laws. Combined with Fubini's theorem, this
computes expected values of functions of independent random variables; for instance
$E f(X_1) g(X_2) = E f(X_1) \, E g(X_2)$ for nonnegative or suitably integrable $f$ and $g$. The proof compares the two
measures on products of Borel sets, a π-system that generates the Borel sets of $\mathbb R^n$.

## Statements

- [Joint law of a finite independent family of random variables](map-fun-eq-pi-map.md)
- [Robust objective of a piecewise-constant surrogate](expectation-of-a-finite-box-partition.md) — Finite-valued expectation formula for the product-law model.

## Background

- [Independence](../independence/README.md): independent random variables
- [Probability measures](../../probability-measures/README.md): laws of random variables

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 2.1.11 (version read: the author's January 2019 PDF).
