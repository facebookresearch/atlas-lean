# Product upper bound on a compact set

Let $X$ and $Y$ be regular topological spaces with measurable open sets, at least one of them
second countable, and let probability measures $\mu_n$ on $X$ and $\nu_n$ on $Y$ satisfy the
[large deviation principle](../large-deviation-principle/satisfies-ldp.md) with rate functions $I$
and $J$. Let $D \subseteq X \times Y$ be compact and $q \in \mathbb{R}$ with $q < I(x) + J(y)$
for every $(x, y) \in D$. Then there is a finite constant $M$ such that, for all sufficiently large
$n$, $(\mu_n \otimes \nu_n)(D) \le M e^{-nq}$.
