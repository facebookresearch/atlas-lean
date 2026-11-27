# Invasion-rate classification of stochastic Lotka–Volterra food chains with intraspecific competition

**Model.** For $n \ge 2$ species with densities $X_1$ (prey) and $X_2,\dots,X_n$ (predators, each eating the one below),

$$dX_1 = X_1(a_{10} - a_{11}X_1 - a_{12}X_2)\,dt + X_1\,dE_1,$$

$$dX_i = X_i(-a_{i0} + a_{i,i-1}X_{i-1} - a_{ii}X_i - a_{i,i+1}X_{i+1})\,dt + X_i\,dE_i, \quad 2 \le i \le n,$$

with $a_{n,n+1} = 0$, all $a_{ij} > 0$ (in particular every species has intraspecific competition $a_{ii} > 0$), and $\mathbf E = \Gamma^\top\mathbf B$ for a standard Brownian motion $\mathbf B$, with covariance $\Sigma = \Gamma^\top\Gamma = (\sigma_{ij})$. Define the noise-corrected rates $\tilde a_{10} = a_{10} - \sigma_{11}/2$ and $\tilde a_{j0} = a_{j0} + \sigma_{jj}/2$ for $j \ge 2$. For each $j$ the tridiagonal linear system

$$-a_{11}x_1 - a_{12}x_2 = -\tilde a_{10}, \qquad a_{i,i-1}x_{i-1} - a_{ii}x_i - a_{i,i+1}x_{i+1} = \tilde a_{i0} \ (2 \le i < j), \qquad a_{j,j-1}x_{j-1} - a_{jj}x_j = \tilde a_{j0}$$

has a unique solution $(x^{(j)}_1,\dots,x^{(j)}_j)$. The **invasion rate** of species $j+1$ into the chain $X_1,\dots,X_j$ is

$$\mathcal I_1 = \tilde a_{10}, \qquad \mathcal I_{j+1} = -\tilde a_{j+1,0} + a_{j+1,j}\,x^{(j)}_j.$$

One has $x^{(j+1)}_{j+1} = \mathcal I_{j+1}/(a_{j+1,j+1} + a_{j+1,j}c'_j)$ for an explicit $c'_j > 0$, so $x^{(j+1)}_{j+1} > 0$ exactly when $\mathcal I_{j+1} > 0$.

**Theorem.** Start from a strictly positive initial condition.

1. If $\mathcal I_n > 0$, the whole chain is persistent in probability and, almost surely,

$$\lim_{t\to\infty}\frac1t\int_0^t X_k(s)\,ds = x^{(n)}_k > 0, \qquad k = 1,\dots,n.$$

If moreover $\Sigma$ is positive definite, the chain is strongly stochastically persistent and its transition probabilities converge exponentially fast in total variation to a unique invariant probability measure on $(0,\infty)^n$.

2. If $\mathcal I_{j^*} > 0$ and $\mathcal I_{j^*+1} < 0$ for some $0 \le j^* < n$ (with $\mathcal I_0 > 0$ by convention), then $X_{j^*+1},\dots,X_n$ go extinct almost surely, exponentially fast with rates $\mathcal I_{j^*+1}, -\tilde a_{j^*+2,0},\dots,-\tilde a_{n0}$; the subchain $X_1,\dots,X_{j^*}$ is persistent in probability, and the time averages converge to $x^{(j^*)}_i$ for $i \le j^*$ and to $0$ for $i > j^*$.

Because the invasion rates are tested in order, the top predator persists only if every intermediate species can invade the chain below it.

## Expansion

For an ergodic invariant measure $\mu$ on a boundary face, the invasion rate of an absent species $i$ is $\int f_i\,d\mu - \sigma_{ii}/2$ (or $+$ for deaths, as encoded in $\tilde a$). Itô's formula applied to $\log X_k$ and the fact that $\frac1t\log X_k(t) \to 0$ under persistence show that the time-average densities on a persistent subchain solve the noise-corrected equilibrium equations, giving $x^{(j)}$; plugging into the predator's per-capita rate gives $\mathcal I_{j+1}$. General invasion-rate theory for stochastic Kolmogorov systems then yields persistence when all boundary measures are invadable and extinction otherwise. Intraspecific competition among predators makes every subchain's equilibrium system uniquely solvable, which is what makes the classification complete.

## Sources

- Alexandru Hening, Dang H. Nguyen, "Persistence in Stochastic Lotka–Volterra Food Chains with Intraspecific Competition", Bulletin of Mathematical Biology 80 (2018), 2527–2560, <https://doi.org/10.1007/s11538-018-0468-5>. Published version of arXiv:1704.07501, cited next; locators there refer to the arXiv version.
- Alexandru Hening, Dang H. Nguyen, "Persistence in Stochastic Lotka--Volterra food chains with intraspecific competition", arXiv (2017). Equation for the invasion rates, Theorem 1.1, Propositions 3.1–3.2. <https://doi.org/10.48550/arXiv.1704.07501>
