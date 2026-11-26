# NIMFA equations and their spectral epidemic threshold

**Equations.** Let $G$ be an undirected graph on $N$ nodes with symmetric adjacency matrix $A = (a_{ij})$, $a_{ij} \in \{0, 1\}$, and let each infected node infect each neighbour at rate $\beta > 0$ and recover at rate $\delta > 0$; write $\tau = \beta/\delta$ for the effective infection rate. NIMFA approximates the infection probability $v_i(t)$ of node $i$ by

$$\frac{dv_i}{dt} = -\delta\, v_i + \beta\,(1 - v_i) \sum_{j=1}^{N} a_{ij} v_j, \qquad i = 1, \dots, N,$$

or in vector form $\dot v = (\beta A - \delta I) v - \beta\, \mathrm{diag}(v) A v$. The cube $[0, 1]^N$ is forward invariant.

**Steady states.** A non-zero steady state $v_\infty$ satisfies, for every $i$,

$$v_{\infty, i} = 1 - \frac{1}{1 + \tau \sum_j a_{ij} v_{\infty, j}} .$$

**Threshold theorem.** Let $\lambda_1$ be the largest eigenvalue (spectral radius) of $A$ and assume $G$ connected. Define the NIMFA epidemic threshold $\tau_c^{(1)} = 1/\lambda_1$.

- If $\tau \le \tau_c^{(1)}$, the origin is the only steady state in $[0, 1]^N$ and every solution converges to $0$.
- If $\tau > \tau_c^{(1)}$, there is a unique steady state $v_\infty \in (0, 1)^N$, and every solution with $v(0) \in [0, 1]^N \setminus \{0\}$ converges to it; the origin is unstable.

For a $k$-regular graph $\lambda_1 = k$ and $v_{\infty, i} = 1 - 1/(\tau k)$ for all $i$, the homogeneous mean-field SIS result.

## Expansion

The linearization at the origin is $\dot v = (\beta A - \delta I) v$, whose largest eigenvalue $\beta\lambda_1 - \delta$ changes sign at $\tau = 1/\lambda_1$; the Perron–Frobenius eigenvector of $A$ is positive, so above threshold the instability points into the interior of the cube. Below threshold, $\dot v \le (\beta A - \delta I) v$ componentwise on $[0, 1]^N$ and comparison with the linear system gives decay. Above threshold, the vector field is cooperative (off-diagonal Jacobian entries $\beta(1 - v_i) a_{ij} \ge 0$) and the right-hand side is strictly concave along rays, which yields uniqueness and global attractivity of the interior equilibrium (the Lajmanovich–Yorke theorem for multigroup SIS models). The independence closure makes NIMFA an upper bound on the exact SIS infection probabilities, so $1/\lambda_1$ is a lower bound for the epidemic threshold of the exact process. Near $\tau_c^{(1)}$ the steady state is aligned with the principal eigenvector, which is the regime in which time-dependent NIMFA solutions can be approximated in closed form.

## Sources

- B. Prasse, P. Van Mieghem, "Time-dependent solution of the NIMFA equations around the epidemic threshold", Journal of Mathematical Biology (2020), <https://doi.org/10.1007/s00285-020-01542-6> (PMC7716943).
- P. Van Mieghem, J. Omic, R. Kooij, "Virus spread in networks", IEEE/ACM Transactions on Networking 17 (2009) 1–14.
- A. Lajmanovich, J. A. Yorke, "A deterministic model for gonorrhea in a nonhomogeneous population", Mathematical Biosciences 28 (1976) 221–236.
