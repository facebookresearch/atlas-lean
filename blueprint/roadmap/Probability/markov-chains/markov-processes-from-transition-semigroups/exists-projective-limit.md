# Kolmogorov extension for Markov semigroup laws

Let $E$ be a Polish space with its Borel $\sigma$-algebra and $(K_t)_{t \ge 0}$ a family of Markov
kernels on $E$ satisfying the Chapman–Kolmogorov equations
$K_{s+t}(x, A) = \int_E K_s(x, dy)\, K_t(y, A)$ for all $s, t \ge 0$. Then for every $x \in E$
there is a measure $P$ on the path space $E^{[0, \infty)}$ (with the product $\sigma$-algebra) whose
image under the projection to the coordinates in each finite set $J \subset [0, \infty)$ is the
[Markov law at the times $J$](finite-law.md) started from $x$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986,
  Chapter 4, Section 4.1.
