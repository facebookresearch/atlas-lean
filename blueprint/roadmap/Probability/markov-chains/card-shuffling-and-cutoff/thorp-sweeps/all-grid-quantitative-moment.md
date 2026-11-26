# Quantitative all-grid moment estimate under scalar and perturbation bounds

Use the [product-grid and conditional moment definitions](perturbed-grid-conditional-permutations.md). Fix $q=65536000000$, $\theta=1/1600$, $K_0=100000$, $B_0=12800$, $\xi=1/2048000000$, $\rho=1/32768000000$, and $a=1/100$, $c_0=e_0=a/100$. The scale $r$ is a natural number satisfying $r\ge2$, and $l=r\log2$ satisfies $l\ge1$, $l\ge(2/e_0)^2$, $l\ge4/e_0$, and $3\log2+2(K_0+1+\log4)\le\theta l/8$. Require every real $s\ge2^r$ to satisfy

$$
\begin{gathered}
s\ge2,\quad \log s\le s^{\theta/4},\quad 2\le s^{\theta/4},\quad B_0+1\le s^{\theta/2},\quad 4s^{-1/(4B_0)}\le\theta/(64B_0),\\
\log(1+2B_0)+\log2\le\xi\log s,\quad s^{-\xi}\le1/8,\quad R\le\xi\log s/16,\quad \log2\le\xi\log s/8,
\end{gathered}
$$

where $R=\log2+B_0(K_0+1+\log4+\log(16e^2)+\log(1+16e^2))$. In addition, for the size $s$ of each allowed grid require $\log s\ge1$ and

$$
100004s^{1-a/4}\le s^{1-1/1600},\quad
2(4(2q+1)+82c_0)s^{4/5+2a}\log(s+1)\le s^{9/10},\quad
s^{9/10}+s^{1-a/2}\log s\le s^{1-a/4}/(20\sqrt{\log s}).
$$

Assume $0<z_*\le 1/[4((2^{2r})!)^2]$. For all allowed grids of width (number of coordinates) at most $B_0$, all $z\in[0,z_*]$, and every nonempty set of line-permutation choices, require that the sum of absolute differences of the $z$-law and the $0$-law conditioned on that event be strictly less than $s^{-2\rho s}(s^\rho-1)$ for $s>1$ (one otherwise). This sum is not halved. Then for every allowed grid, every $z\in[0,z_*]$, every feasible disjoint trajectory system and every unitary irreducible residual representation, the unlogged Schatten moment is at most $\exp(-c(s)\log D+e(s)h\log s-C(H))$.

**Conventions.** Divide the compatible weighted sum by its event probability before taking the Schatten moment. Do not divide the trace by the representation dimension. The numeric conditions are hypotheses here, not claimed automatically.

## Depends on

- [Conditional permutations on product grids](perturbed-grid-conditional-permutations.md)

- [Coordinate-fiber sweeps on the binary cube](binary-sweep-step-law.md)

## Expansion

Take the stated event-distance, scale and scalar bounds as hypotheses; do not re-prove the perturbation premise in this theorem. Isolate the bounded-width sparse moment estimate with the specified slack and the operator comparison at a coordinate split. Give a uniform dimension-saving induction preserving the feasible-trajectory cost and the conditional normalization. Retain the unlogged moment, including its zero case.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CoordinateSweeps.lean#L299-L305)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/238.md)
- [Accompanying manuscript: Conditional coordinate sweeps and analytic transfer](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Conditional-coordinate-sweeps-and-analytic-transfer-September-26-2026/main.pdf)
