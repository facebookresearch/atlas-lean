# Riccati-inequality solution of the stochastic minimax evolutionary game for a gene network

**Model.** A linearised gene network with state $x(t) \in \mathbb{R}^n$ around the phenotype $x_e = 0$ accumulates heritable interaction changes as a weighted Poisson point process:

$$\frac{dx}{dt} = A x + \sum_{k=1}^{N(t)} A_k\, x + B v(t) = A x + u(t) + \sum_{k=1}^{N_2(t)} A_k\, x + B v(t),$$

where $N = N_1 + N_2$ splits into selected variations (rate $\lambda_1$), whose total effect $u(t) = \sum_{k \le N_1(t)} A_k x$ is the **evolutionary strategy**, and neutral variations (Poisson rate $\lambda_2$); $v \in L^2[0, t_p]$ is an unknown environmental disturbance and $B$ its coupling matrix. With a positive definite weight $Q$, the **evolution level** is the worst-case gain

$$e = \max_{v \in L^2[0, t_p]} \frac{E\int_0^{t_p} \big(\tilde x^\top Q \tilde x + u^\top u\big)\,dt}{E\,\tilde x(0)^\top \tilde x(0) + E\int_0^{t_p} v^\top v\,dt},$$

fitness (phenotypic robustness) is $1/e$, and the **evolvability** $e_o$ is the minimum of $e$ over strategies $u$.

**Proposition.** Fix $\bar e > 0$ and let $N_{2p}$ be the number of neutral variations up to the present time $t_p$. If a matrix $P$ with $0 < P \le \bar e I$ satisfies the Riccati-like inequality

$$A^\top P + P A - P P + \frac{1}{\bar e} P B B^\top P + Q + \lambda_2 \sum_{k=1}^{N_{2p}} A_k^\top P A_k \le 0,$$

then the minimax strategy and the worst-case disturbance are

$$u^*(t) = -P x(t), \qquad v^*(t) = \frac{1}{\bar e} B^\top P x(t),$$

and the evolution level is at most $\bar e$; decreasing $\bar e$ while the inequality stays feasible approaches $e_o$. By the Schur complement the inequality is equivalent to a linear matrix inequality in $X = P^{-1}$.

## Expansion

This is a stochastic $H_\infty$ (soft-constrained Nash game) problem: the constrained minimax in $e \le \bar e$ is rewritten as $\min_u \max_v E\int (\tilde x^\top Q\tilde x + u^\top u - \bar e\, v^\top v)\,dt \le \bar e\, E\,\tilde x(0)^\top\tilde x(0)$, and completing squares in a quadratic Lyapunov function $\tilde x^\top P \tilde x$, with Itô-type jump terms for the Poisson variations, gives the inequality. The term $\lambda_2 \sum A_k^\top P A_k$ is the cost of neutral variations; the selected strategy $-P$ acts as negative feedback, so a larger feasible $P$ buffers both genetic and environmental perturbations. The source gives the nonlinear version via a Hamilton–Jacobi inequality and a polytopic global-linearisation version with one Riccati inequality per vertex.

## Sources

- B.-S. Chen, S.-J. Ho, *The stochastic evolutionary game for a population of biological networks under natural selection*, Evol. Bioinform. 10 (2014), 17–38 (Eqs. (7)–(19), Proposition 1; Propositions 2–3 for the nonlinear and polytopic cases). <https://doi.org/10.4137/ebo.s13227> (PMCID: PMC3928070)
