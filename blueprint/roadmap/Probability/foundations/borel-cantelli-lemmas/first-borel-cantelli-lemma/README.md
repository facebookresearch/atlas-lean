# First Borel–Cantelli lemma

Let $\mu$ be an outer measure on a set, or a measure, and let $s_1, s_2, \dots$ be sets with
$\sum_i \mu(s_i) < \infty$. Then the set $\limsup_i s_i = \bigcap_n \bigcup_{i \ge n} s_i$ of points that lie in infinitely
many $s_i$ has measure $0$. No measurability of the sets is needed.

## Idea

In probability: if $A_1, A_2, \dots$ are events with $\sum_n P(A_n) < \infty$, then
$P(A_n \text{ infinitely often}) = 0$, so almost surely only finitely many of the events occur. The probability that
some $A_n$ with $n \ge m$ occurs is at most $\sum_{n \ge m} P(A_n)$, which tends to $0$; no independence is needed. A
typical use is to prove almost sure convergence: if $\sum_n P(|X_n - X| > \varepsilon) < \infty$ for every
$\varepsilon > 0$, then $X_n \to X$ almost surely. For independent events the second Borel–Cantelli lemma gives a
converse.

## Statements

- [First Borel–Cantelli lemma for outer measures](measure-limsup-at-top-eq-zero.md)

## Background

- [Probability measures](../../probability-measures/README.md): probability measures

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 2.3.1 (version read: the author's January 2019 PDF).
