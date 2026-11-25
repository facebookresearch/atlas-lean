# Exposure Probability eq sum

Let $U$ be a finite set of units, $\Omega$ a set of assignments, $\Delta$ a set of exposure values, and $e : U \times \Omega \to \Delta$ an exposure mapping, so $e_i(z)$ is the exposure of unit $i$ under assignment $z$. Assume moreover that $\Omega$ is finite, and let $p$ be a probability mass function on $\Omega$. Then for every unit $i$ and exposure $d$, the exposure probability (the inclusion probability of $i$ in the exposed set $\{j : e_j(z) = d\}$ under $z \sim p$) is the total design mass of the assignments that give unit $i$ exposure $d$:

$$\pi_i(d) = \sum_{z \in \Omega} \mathbf 1[e_i(z) = d]\, p(z).$$
