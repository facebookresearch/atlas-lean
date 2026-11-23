# Monge–Kantorovich existence theorem

Let $X$ and $Y$ be Polish spaces with their Borel
$\sigma$-algebras, let $P$ and $Q$ be probability measures on $X$ and $Y$, and let
$c \colon X \times Y \to [0, \infty]$ be continuous. Then there is a coupling $\pi$ of $P$ and $Q$
whose Kantorovich cost $\int c \, d\pi$ is at most the Kantorovich cost $\int c \, d\pi'$ of every
coupling $\pi'$ of $P$ and $Q$: the Kantorovich cost attains its minimum on the set of couplings
of $P$ and $Q$.

Proof: by the [bridge between the two descriptions of couplings](mem-couplings-iff.md), this is
the [existence of an optimal coupling](exists-is-coupling-forall-lintegral-le.md) for the
probability measures $P$ and $Q$, which follows Villani's proof of Theorem 4.1: the couplings form
a tight, weakly closed set, hence a compact one, on which the total cost is lower semicontinuous.

## Sources

- L. V. Kantorovich (1942), after G. Monge (1781). Listed as §73 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Problem `monge_kantorovich` of the lean-eval benchmark.
- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Theorem 4.1.
