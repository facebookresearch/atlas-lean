# Kolmogorov's zero–one law

Let $\mu$ be a measure on a measurable space $\Omega$, and let $(\mathcal M_i)$ be a family of sub-σ-algebras of
the σ-algebra on which $\mu$ is defined, independent with respect to $\mu$ and indexed by a nonempty join semilattice
with no largest element, such as $\mathbb N$. Then every set of the tail σ-algebra $\bigcap_n \bigvee_{i \ge n} \mathcal M_i$
has measure $0$ or $1$.

## Idea

For a sequence $X_1, X_2, \dots$ of independent random variables, take $\mathcal M_i = \sigma(X_i)$: then
$\bigvee_{i \ge n} \sigma(X_i) = \sigma(X_n, X_{n+1}, \dots)$, and every event of the tail σ-field
$\mathcal T = \bigcap_n \sigma(X_n, X_{n+1}, \dots)$ has probability $0$ or $1$. A tail event is determined by
$(X_n, X_{n+1}, \dots)$ for every $n$, so altering finitely many of the $X_n$ does not change whether it occurs; examples
are $\{X_n \in B_n \text{ infinitely often}\}$ for Borel sets $B_n$ and the event that $\sum_n X_n$ converges. The proof shows that $\mathcal T$ is independent of each
$\sigma(X_1, \dots, X_k)$, hence of $\sigma(X_1, X_2, \dots)$, which contains $\mathcal T$; so a tail event $A$ is
independent of itself, and $P(A) = P(A)^2$.

## Statements

- [Kolmogorov's zero–one law for independent σ-algebras](measure-zero-or-one-of-measurable-set-li.md)

## Background

- [Independence](../independent-events-and-random-variables/independence/README.md): independence
- [Independence from π-systems](../independent-events-and-random-variables/pi-systems-and-independence/README.md): the π-system criterion and functions of disjoint blocks, used in the proof
- [Probability measures](../probability-measures/README.md): probability measures

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Section 2.5 (the tail σ-field) and Theorem 2.5.3 (version read: the author's January 2019 PDF).
