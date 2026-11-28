# Brownian adapter

**Brownian adapter.** Let $B = (B_t)_{t \ge 0}$ be a real Brownian motion on a measure space $(\Omega', P')$. Then there is a measurable map $Z : \Omega' \to C([0,1], \mathbb{R})$, for the Borel σ-algebra of the uniform topology on $C([0,1], \mathbb{R})$, such that:

- for $P'$-almost every $\omega$, $Z(\omega)(t) = B_t(\omega)$ for all $t \in [0,1]$;
- for every finite set $I \subseteq [0,1]$ and all coefficients $(c_s)_{s \in I}$, the linear combination $\omega \mapsto \sum_{s \in I} c_s Z(\omega)(s)$ has law under $P'$ the centered Gaussian

$$\mathcal{N}\Big(0, \sum_{s \in I} \sum_{u \in I} c_s c_u \min(s, u)\Big),$$

where the variance is the positive part of the double sum.

Thus $Z$ is a measurable version of the almost surely continuous path map $\omega \mapsto (t \mapsto B_t(\omega))$ restricted to $[0,1]$, with the finite-dimensional Gaussian laws of Brownian motion.

## Sources

- the finite-dimensional distributions of Brownian motion (Wiener measure on $C[0,1]$) are centered Gaussian with covariance $\min(s, t)$, and a linear functional $\sum_s c_s Z_s$ of a centered Gaussian vector is centered normal with variance $\sum_s \sum_u c_s c_u \operatorname{Cov}(Z_s, Z_u)$: Billingsley, *Convergence of Probability Measures*, 2nd ed., Section 8 (Wiener measure).
