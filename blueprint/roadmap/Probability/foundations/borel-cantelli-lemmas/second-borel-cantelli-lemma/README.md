# Second Borel–Cantelli lemma

Let $s_1, s_2, \dots$ be mutually independent measurable sets of a probability space $(\Omega, \mu)$. If
$\sum_n \mu(s_n) = \infty$, then the set $\limsup_n s_n = \bigcap_m \bigcup_{n \ge m} s_n$ of points that lie in infinitely
many $s_n$ has measure $1$.

## Idea

In the language of events: if $A_1, A_2, \dots$ are independent and $\sum_n P(A_n) = \infty$, then almost
surely infinitely many of them occur. Together with the first Borel–Cantelli lemma this gives a dichotomy for
independent events: $P(A_n \text{ infinitely often})$ is $0$ or $1$ according as $\sum_n P(A_n)$ converges or diverges.
Independence cannot be dropped: if every $A_n$ is one event $A$ with $0 < P(A) < 1$, the sum diverges but
$P(A_n \text{ infinitely often}) = P(A)$. The proof bounds the probability that none of $A_m, \dots, A_M$ occurs by
$\prod_{n=m}^{M} (1 - P(A_n)) \le \exp\big(-\sum_{n=m}^{M} P(A_n)\big)$, which tends to $0$.

## Statements

- [Second Borel–Cantelli lemma for independent measurable sets](measure-limsup-eq-one.md)

## Background

- [Independence](../../independent-events-and-random-variables/independence/README.md): independent events
- [Independence from π-systems](../../independent-events-and-random-variables/pi-systems-and-independence/README.md): complements of independent events are independent
- [Probability measures](../../probability-measures/README.md): probability measures

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 2.3.7 (version read: the author's January 2019 PDF).
