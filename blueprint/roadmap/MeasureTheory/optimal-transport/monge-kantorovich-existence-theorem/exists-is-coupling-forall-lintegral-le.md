# Existence of an optimal coupling

Let $X$ and $Y$ be Polish spaces with Borel probability measures $\mu$ and $\nu$, and let
$c : X \times Y \to [0, \infty]$ be continuous. Then there is a coupling $\pi$ of $\mu$ and $\nu$ such
that $\int c \, d\pi \le \int c \, d\pi'$ for every coupling $\pi'$ of $\mu$ and $\nu$.

Proof: the set of couplings is [tight](is-tight-measure-set-set-of-is-coupling.md) and
[closed](is-closed-set-of-is-coupling.md), hence compact by Prokhorov's theorem; it is nonempty
(it contains $\mu \otimes \nu$); and the total cost is
[lower semicontinuous](lower-semicontinuous-lintegral.md), so it attains its minimum.

The [Monge–Kantorovich existence theorem](monge-kantorovich-exists.md) of this topic, stated with
its own coupling and cost definitions, is deduced from it. Villani's
Theorem 4.1 allows a lower semicontinuous cost bounded below by $a(x) + b(y)$ with $a, b$
integrable and upper semicontinuous; the statement above is the case $a = b = 0$ with a continuous cost.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Theorem 4.1, Lemmas 4.3 and 4.4.
