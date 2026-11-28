# Ribosome flow model of extended objects with drop-off

**Model (RFMEOD).** A chain of $n$ sites is traversed left to right by particles of size $\ell$, a particle being located at the site of its leftmost end (its *reader*). Let $x_i(t) \in [0,1]$ be the reader density at site $i$ and $y_i = x_{i-\ell+1} + \dots + x_i$ the coverage density (with $x_j = 0$ for $j \le 0$ and $y_i = 0$ for $i > n$). With hopping rates $\lambda_0,\dots,\lambda_n > 0$ and drop-off rates $\alpha_1,\dots,\alpha_n \ge 0$, set

$$f_0 = \lambda_0(1 - y_\ell), \qquad f_i = \lambda_i x_i(1 - y_{i+\ell}) \;(1 \le i \le n-1), \qquad f_n = \lambda_n x_n, \qquad g_i = \alpha_i x_i,$$

and

$$\dot x_i = f_{i-1}(x) - f_i(x) - g_i(x_i), \qquad i = 1,\dots,n.$$

The protein production (output) rate is $R(t) = (\lambda_n + \alpha_n)\,x_n(t)$. This is the interaction-free case $q = r = 1$ of the extended model EFEIOD, in which the factors $q$ and $r$ scale the rates of forming and breaking contacts with neighbouring particles.

**State space.** Let $P$ be the $n \times n$ lower-triangular matrix with ones on the main diagonal and the $\ell - 1$ subdiagonals below it, so $(Px)_i = y_i$, and $H = \{x \in [0,1]^n : Px \in [0,1]^n\}$. $H$ is compact, convex and forward invariant, and trajectories from $\partial H$ enter the interior of $H$ immediately (Propositions 1–2).

**Theorem 1 (global stability).** For $q, r > 0$, in particular for the RFMEOD, there is a unique steady state $e \in \mathrm{int}(H)$ and $\lim_{t \to \infty} x(t, a) = e$ for every initial condition $a \in H$. The proof shows the system is contractive in the $L_1$ norm after any transient $\tau > 0$, with overshoot $1 + \epsilon$ (Proposition 3).

**Sensitivity of the steady state (Propositions 5–7).** For the RFMEOD with steady-state output rate $R = (\lambda_n + \alpha_n) e_n$:

- $\partial R/\partial \alpha_i < 0$ for $i = 1,\dots,n-1$: more drop-off anywhere except the last site lowers production;
- $\partial R/\partial \lambda_i > 0$ for $i = 0,\dots,n$: speeding up any step, including initiation $\lambda_0$, raises production;
- if all $\lambda_i = \lambda$ and $\alpha_i = \alpha \ne 0$, then $e_i = \left(\frac{\lambda + \alpha}{\lambda}\right)^{n-i} e_n$ for $i = n-\ell+1,\dots,n$, the reader densities decrease strictly along the chain, $e_1 > e_2 > \dots > e_n$, and $y_\ell > y_{\ell+1} > \dots > y_n$.

## Expansion

The last $\ell - 1$ equations are linear because a particle reading one of the last codons has nothing ahead of it; at steady state $\lambda e_{i-1} = (\lambda + \alpha) e_i$ there, which gives the geometric profile. Monotonicity of $R$ is proved by contradiction: comparing two steady states differing in one rate, the flow balance $f_{i-1}(e) = f_i(e) + g_i(e_i)$ propagates an assumed inequality on $e_n$ backwards along the chain and ends in a contradiction with the inflow equation at site $1$. With $\ell = 1$, $\alpha_i = 0$ and $q = r = 1$ the model reduces to the classical ribosome flow model.

## Sources

- A. Jain, A. K. Gupta, "Modeling transport of extended interacting objects with drop-off phenomenon", PLoS ONE 17 (2022) e0267858, Eqs. (8)–(11), (21)–(24), Propositions 1–3 and 5–7 and Theorem 1, <https://doi.org/10.1371/journal.pone.0267858>, PMCID PMC9060384.
