# Regret matching meets Blackwell's condition with equality

Playing unconditional regret matching computed from $x$, against any opponent action $b$, the
expected regret vector $y$ is orthogonal to $x^+$:
$\langle x^+, y\rangle = \sum_k x_k^+ \bigl(\sum_a q(a) c(a, b) - c(k, b)\bigr) = 0$ for
$q = x^+/\sum_l x_l^+$. Since $x - \min(x, 0) = x^+$ and $\langle x^+, \min(x, 0)\rangle = 0$,
this says that $y$ lies on the boundary of the half-space through the nearest point of the
orthant with outer normal $x^+$: regret matching is the Blackwell strategy for the orthant.

## Background

- [Blackwell's half-space step](../blackwell-approachability/exists-inner-sub-nonpos-of-enforceable.md):
  the general step this specialises.

## Sources

- S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium", Econometrica 68(5) (2000), 1127–1150, §3, Theorem B and its proof via Blackwell's theorem.
- S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, §10.1, Proposition 4 and the remark after it.
