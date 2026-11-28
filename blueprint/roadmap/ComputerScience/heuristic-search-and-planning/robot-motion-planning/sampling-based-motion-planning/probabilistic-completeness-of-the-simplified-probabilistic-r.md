# Probabilistic completeness of the simplified probabilistic roadmap

Consider a robustly feasible path planning problem $(X_{\mathrm{free}}, x_{\mathrm{init}}, X_{\mathrm{goal}})$
and the simplified probabilistic roadmap algorithm with a fixed connection radius $r > 0$ and $n$ independent
uniform samples. There exist $a > 0$ and $n_0 \in \mathbb{N}$ such that for all $n > n_0$ the probability that the
algorithm fails to return a feasible path connecting $x_{\mathrm{init}}$ to $X_{\mathrm{goal}}$ is at most
$e^{-an}$.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Robust feasibility of path planning problems.
- Statement prerequisite: robust feasibility for goal regions of positive volume, as in the source, not only for point goals.

## Sources

- S. Karaman and E. Frazzoli, *Sampling-based algorithms for optimal motion planning*, Int. J. Robotics Res. 30(7) (2011); arXiv:1105.1186, Theorem 15 (after Kavraki, Kolountzakis and Latombe, 1998). <https://arxiv.org/abs/1105.1186>
