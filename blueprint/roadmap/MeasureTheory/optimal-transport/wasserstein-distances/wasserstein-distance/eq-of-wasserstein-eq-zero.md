# The Wasserstein distance separates probability measures

Let $X$ be a second-countable pseudo-extended metric space with its Borel σ-algebra and $p \ge 1$.
If $W_p(\mu, \nu) = 0$ then $\mu = \nu$.

Villani's argument takes an optimal coupling, which must then be concentrated on the diagonal. A
proof avoiding the existence theorem: $W_1 \le W_p$ gives $W_1(\mu, \nu) = 0$, so every bounded
Lipschitz test function has the same integral against $\mu$ and $\nu$; the thickened indicators of a
closed set $F$ are such functions and their integrals converge to $\mu(F)$ and $\nu(F)$; closed sets
generate the Borel σ-algebra. Together with symmetry, the triangle inequality and $W_p(\mu, \mu) = 0$,
this shows that $W_p$ is an extended metric on Borel probability measures over a Polish space.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Chapter 6, proof that $W_p$ satisfies the axioms of a distance, after Definition 6.1.
