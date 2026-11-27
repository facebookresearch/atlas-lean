# Positivstellensatz (sum-of-squares) refutations

Let $\mathcal{R}$ be an ordered commutative ring, $I$ a set of inequality constraints $f \ge 0$ and $E$ a set of equations $g = 0$ in $\mathcal{R}[x]$. A *Positivstellensatz refutation* is an identity

$$\sum_j h_j g_j + \sum_k c_k\, s_k^2 \prod_{f \in S_k} f = -1$$

with $g_j \in E$, finite sets $S_k \subseteq I$ and weights $c_k \ge 0$. It has *degree at most $d$* if every summand $h_j g_j$ and $s_k^2 \prod_{f\in S_k} f$ has total degree at most $d$. With $I = \emptyset$ this is a *sum-of-squares* (SOS) refutation of the equations. Refutations are sound: at a common solution the left side is nonnegative.

## Sources

- D. Grigoriev, E. A. Hirsch and D. V. Pasechnik, "Complexity of Semialgebraic Proofs", Moscow Mathematical Journal 2(4), 647–679, 2002.
- B. Barak and D. Steurer, Proofs, Beliefs, and Algorithms through the Lens of Sum-of-Squares, lecture notes, 2016.
