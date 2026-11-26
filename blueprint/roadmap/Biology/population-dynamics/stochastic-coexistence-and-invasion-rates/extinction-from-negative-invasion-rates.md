# Extinction from negative weighted invasion rates

Let $X(t) = (X_1(t), \dots, X_n(t)) \in \mathbb{R}_+^n$ be species densities and $Y(t) \in \mathbb{R}^{\kappa_0}$ an auxiliary
variable (feedbacks, forcing, structure), driven by i.i.d. environmental states $\xi(0), \xi(1), \dots$ in a Polish space $\Xi$:
$$X_i(t+1) = X_i(t)\, F_i(X(t), Y(t), \xi(t)), \quad i = 1, \dots, n, \qquad Y(t+1) = G(X(t), Y(t), \xi(t)).$$
Assume each fitness $F_i(z, \xi)$ is strictly positive, continuous in $z = (x,y)$ and jointly measurable, $G$ is continuous in $z$ and
measurable, and there is a Lyapunov function $V : S \to \mathbb{R}_+$ on $S = \mathbb{R}_+^n \times \mathbb{R}^{\kappa_0}$ with
$V(x,y) \ge |x|^{\gamma_1} + 1$, $V(z) \to \infty$ as $|z| \to \infty$, and
$E[V(x \circ F(z,\xi), G(z,\xi))\, h(z,\xi)] \le \rho V(z) + C$ for some $\rho \in (0,1)$, $C, \gamma_1, \gamma_3 > 0$, where
$h(z,\xi) = \bigl(\max_i \max\{F_i(z,\xi), F_i(z,\xi)^{-1}\}\bigr)^{\gamma_3}$ and $\circ$ is the Hadamard product. Let
$S_0 = \{ \min_i x_i = 0 \}$ be the extinction set. For an ergodic invariant probability measure $\mu$ of $Z = (X, Y)$, its species
support is $S(\mu) = \{ i : \mu(x_i > 0) = 1 \}$ and the **invasion rate** of species $i$ is
$$r_i(\mu) = \int_S E[\log F_i(z, \xi(1))]\, \mu(dz).$$
It exists, is finite, and $r_i(\mu) = 0$ for every $i \in S(\mu)$. Let $\mathcal M$ be the set of ergodic invariant probability measures
supported on $S_0$.

Assume in addition the extinction-set Lyapunov condition of the paper (there are $\phi : S \to (0,\infty)$ and constants with
$E_z V(Z(1)) \le V(z) - \phi(z) + C$ and a matching bound on fluctuations), and that $S_0$ is *accessible*: from every
$z \in S \setminus S_0$ the process reaches every neighbourhood of $S_0$ with positive probability.

**Theorem (extinction).** If there are $p_1, \dots, p_n > 0$ such that
$$\sum_{i=1}^n p_i\, r_i(\mu) < 0 \quad \text{for every ergodic invariant probability measure } \mu \text{ supported on } S_0,$$
then there is $\alpha > 0$ such that for every initial state $z \in S$,
$$\Pr_z\Bigl( \limsup_{t\to\infty} \frac{\log \min_i X_i(t)}{t} = -\alpha \Bigr) = 1,$$
i.e. with probability one at least one species goes extinct exponentially fast.

## Depends on

- [Stochastic persistence from positive invasion rates](persistence-from-positive-invasion-rates.md)

## Expansion

The weighted sum $\sum_i p_i \log X_i(t)$ has asymptotic per-step drift $\sum_i p_i r_i(\mu)$ whenever the process is near the boundary and
distributed approximately like $\mu$; a uniformly negative value for all boundary ergodic measures makes the boundary attracting, and
accessibility guarantees the process gets close enough for this drift to take over. Refinements in the paper identify which
subcommunity survives: for a subcommunity $I$ whose ergodic measures cannot be invaded by any outsider, species outside $I$ go extinct
at an exponential rate with probability close to one when starting near that subcommunity. (Hening, Nguyen and Chesson 2021,
Assumption 2.2 and Theorems 2.4–2.5.)

## Sources

- A. Hening, D. H. Nguyen, and P. Chesson, "A general theory of coexistence and extinction for stochastic ecological communities", Journal of Mathematical Biology (2021), <https://doi.org/10.1007/s00285-021-01606-1>.
