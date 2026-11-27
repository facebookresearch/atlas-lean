# Goemans–Williamson Theorem 3.1: expected weight of the random-hyperplane cut

For weights $w_{ij}$ of any sign, unit vectors $v_i \in \mathbb{R}^n$ and a standard Gaussian
vector $r$, the cut $S = \{i : v_i \cdot r \ge 0\}$ has expected weight

$$\mathbb{E}[w(S, \bar S)] = \sum_{i<j} w_{ij} \frac{\arccos(v_i \cdot v_j)}{\pi}.$$

## Informally uses

- [Lemma 3.2](measure-real-sign-ne.md): each pair is separated with probability
  $\arccos(v_i \cdot v_j)/\pi$; Theorem 3.1 follows by linearity of expectation.

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), Theorem 3.1.
