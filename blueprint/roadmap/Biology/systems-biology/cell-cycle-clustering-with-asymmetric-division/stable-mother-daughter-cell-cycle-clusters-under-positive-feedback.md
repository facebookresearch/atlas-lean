# Stable mother–daughter cell-cycle clusters under positive feedback and asymmetric division

**Model.** Each of $n$ cells has a cell-cycle phase $x_i \in [0,1)$, with $1$ denoting division. Fix a *signaling region* $S = [s_1, s_2]$ and a *responsive region* $R = [r_1, r_2]$ with $0 < s_1 < s_2 < r_1 < r_2 < 1$. Let $I = \#\{i : x_i \in S\}/n$ and let $\rho$ be a feedback function; positive feedback means $\rho$ is increasing with $\rho(0) = 0$. Phases advance by

$$\dot x_i = \begin{cases} 1, & x_i \notin R,\\ 1 + \rho(I), & x_i \in R.\end{cases}$$

At division a cell becomes either a *daughter*, reset to phase $0$, or a *mother*, reset to phase $g \in [0,1)$, so mothers reach the next division sooner (asymmetric division as in budding yeast). In the clustered models, cells form clusters that move together; in $\mathbf{C}_f$ daughter clusters stay daughters and mother clusters stay mothers, and in $\mathbf{C}_s$ they switch roles at each division. A *$p{:}q$ perfectly clustered solution* (PCS) is a periodic clustered solution with $p$ mother clusters and $q$ daughter clusters, $p \le q$, timed so that whenever a mother cluster divides and jumps to $g$, a daughter cluster arrives at $g$ at the same instant.

**Theorem.**
1. *(Existence.)* For any feedback function (positive or negative), any $0 < s_1 < s_2 < r_1 < r_2 < 1$ and any $1 \le p \le q$, there is $g \in [0,1)$ for which a $p{:}q$ PCS exists.
2. *(Stability of $1{:}2$ and $2{:}3$ modes.)* In both $\mathbf{C}_f$ and $\mathbf{C}_s$ under positive feedback there exist asymptotically stable $1{:}2$ and $2{:}3$ PCS, with cluster order $r_1 s_1 r_2 s_2 1$ in the cell cycle (each region boundary is crossed in that cyclic order).

## Depends on

## Expansion

Between boundary crossings the clusters move at speed $1$ or $1 + \rho(I)$, with $I$ piecewise constant, so the return map of the cluster configuration to a Poincaré section is piecewise affine and computable explicitly for a fixed event order. Choosing $g$ to equal the phase of a daughter cluster at the moment a mother cluster divides makes the configuration close up, giving existence for every $p \le q$. Linear stability reduces to the eigenvalues of the return-map Jacobian, whose characteristic polynomial has positive coefficients; Anderson's annulus bound ($\min_i a_i/a_{i+1} \le |z| \le \max_i a_i/a_{i+1}$ for zeros of $\sum a_i z^i$ with $a_i > 0$) places all eigenvalues inside the unit disk for the stated order under positive feedback. Without asymmetric division, positive feedback is known to destabilize clustering, so asymmetry is what makes the clusters stable.

## Sources

- G. Dooley, C. Kilton, B. Needham and G. Walther, "Population Structures with Positive Feedback and Asymmetric Division", arXiv:2608.03604 (2026), Theorems 2.5, 2.8, 3.4, 4.4 and Corollary 2.9, <https://doi.org/10.48550/arXiv.2608.03604>.
