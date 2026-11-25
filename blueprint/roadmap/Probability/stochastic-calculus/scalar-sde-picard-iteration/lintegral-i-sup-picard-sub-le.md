# Maximal difference estimate for scalar Picard updates

Let $B$ have real Brownian finite-dimensional laws, be adapted to $(\mathcal F_t)$, and have increments independent of the past filtration. Let $X,Y$ be progressive real processes, continuous on every path, with finite integrated second moments on the horizon $[0,t]$. Let $\sigma,b$ be globally Lipschitz with a common constant $K\ge0$.

Suppose $J,L$ are continuous-path martingales with fixed-time almost-sure equality, at every nonnegative time, to the actual Itô integrals of $\sigma(X)$ and $\sigma(Y)$. For a common deterministic $x$, set

$$U_s=x+J_s+\int_0^s b(X_u)\,du,\qquad
V_s=x+L_s+\int_0^s b(Y_u)\,du.$$

Then, in nonnegative-integral form,

$$\mathbb E\sup_{0\le s\le t}|U_s-V_s|^2
\le 2(4+t)K^2\,\mathbb E\int_0^t|X_s-Y_s|^2\,ds.$$

The initial value cancels. The two-term square bound combines the stochastic maximal estimate, with factor four from Doob, and the ordinary Cauchy–Schwarz estimate, with factor $t$. This estimate needs no completeness or right continuity of the filtration and no path continuity of $B$. It compares actual updates; it does not assume or assert convergence of an iteration.
