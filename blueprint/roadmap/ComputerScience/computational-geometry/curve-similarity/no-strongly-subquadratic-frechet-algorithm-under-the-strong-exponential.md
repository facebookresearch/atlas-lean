# No strongly subquadratic Fréchet algorithm under the strong exponential time hypothesis

Assume the strong exponential time hypothesis, in the form that for no $\delta > 0$ is there an $O^*((2 - \delta)^N)$-time algorithm for CNF-SAT on $N$ variables. Then for no $\delta > 0$ can the Fréchet distance of two polygonal curves with $n$ vertices each be computed in time $O(n^{2 - \delta})$, and no strongly subquadratic algorithm approximates the Fréchet distance within a factor $1.001$ (Bringmann).

## Depends on

- [Fréchet distance of curves](frechet-distance-of-curves.md)
- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)

## Expansion

This page becomes ready once:

- Proof prerequisite: Bringmann's reduction from CNF-SAT to the Fréchet distance of polygonal curves (and to its approximation within $1.001$), as a page of its own.

## Sources

- K. Bringmann, "Why walking the dog takes time: Fréchet distance has no strongly subquadratic algorithms unless SETH fails", arXiv:1404.1448, <https://arxiv.org/abs/1404.1448>: abstract (the conditional lower bound for the continuous and the discrete Fréchet distance and for $1.001$-approximation)
