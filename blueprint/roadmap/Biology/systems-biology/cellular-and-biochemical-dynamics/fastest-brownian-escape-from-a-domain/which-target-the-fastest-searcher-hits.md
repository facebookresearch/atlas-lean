# Which target the fastest searcher hits

**Setting.** Independent and identically distributed searchers each hit one of $m$ targets (or never hit). For a single searcher let $\tau$ be its hitting time, $\kappa \in \{0, \dots, m-1\}$ the target hit, $F(t) = \mathbb{P}(\tau \le t)$ and $F_k(t) = \mathbb{P}(\tau \le t, \kappa = k)$. Assume $F$ is continuous with $F(0) = 0$, so that ties between searchers have probability zero (for $\tau \equiv 1$ all searchers tie and the fastest one is undefined). With $N$ searchers, let $K_N$ be the target hit by the fastest one ($K_N = \infty$ if no searcher ever hits).

**Theorem.**
1. *(Exact formula.)* $\mathbb{P}(K_N = k) = N\int_0^\infty (1 - F(t))^{N-1}\,dF_k(t)$ for $k = 0, \dots, m-1$, and $\mathbb{P}(K_N = \infty) = \mathbb{P}(\tau = \infty)^N$.
2. *(Asymptotics.)* Suppose that as $t \to 0^+$

$$
F(t) \sim A t^{p} e^{-C_0/t}, \qquad F_k(t) \sim B t^{q} e^{-C_k/t},
$$

with $C_k > C_0 > 0$, $A, B > 0$, $p, q \in \mathbb{R}$. Then

$$
\mathbb{P}(K_N = k) \sim \eta\,(\ln N)^{p\beta - q}\, N^{1-\beta} \quad (N \to \infty), \qquad \beta = \frac{C_k}{C_0} > 1, \quad \eta = B\,C_0^{\,q - p\beta} A^{-\beta}\,\beta\,\Gamma(\beta).
$$

3. *(Logarithmic version.)* If only $\lim_{t\to 0^+} t\ln F(t) \ge -C_0$ and $\lim_{t\to 0^+} t\ln F_k(t) \le -C_k$ with $C_k > C_0 > 0$, then $\mathbb{P}(K_N = k) = o(N^{1-\beta+\varepsilon})$ for every $\varepsilon > 0$.

For diffusive searchers (including space-dependent diffusivity and drift, and diffusion on curved Riemannian spaces) the logarithmic hypotheses hold with $C_j$ proportional to $L_j^2$, where $L_j$ is a geodesic distance from the starting locations to target $j$; hence, with target $0$ the closest,

$$
\mathbb{P}(K_N = k) = o\bigl(N^{1 - (L_k/L_0)^2 + \varepsilon}\bigr) \quad \text{for every } \varepsilon > 0,
$$

whatever the targets' sizes or the single-searcher hitting probabilities.

## Depends on

- [Moments of the fastest Brownian escape time](moments-of-the-fastest-brownian-escape-time.md)

## Proof sketch

The fastest searcher hits in time of order $C_0/\ln N$, where only the short-time tails of $F$ and $F_k$ matter. Substituting the tails into the exact integral and changing variables reduces it to a Laplace-type integral $\int t^{q-2}e^{-C_k/t}(1 - At^p e^{-C_0/t})^{N-1}dt$, whose asymptotics produce $N^{-\beta}$ times logarithmic corrections and the gamma-function constant; the factor $N$ in front gives $N^{1-\beta}$. Short-time tails of the form $t^p e^{-L^2/(4Dt)}$ hold for diffusions in quite general geometries (Varadhan-type asymptotics), which is why the result is geometry-independent at leading exponential order: the many-searcher limit replaces hitting probabilities by distances.

## Sources

- Samantha Linn and Sean D. Lawley, "Extreme hitting probabilities for diffusion*", *Journal of Physics A: Mathematical and Theoretical* 55 (2022), 345002, <https://doi.org/10.1088/1751-8121/ac8191>. Preprint version: arXiv:2110.11277 (2021), Proposition 1, Proposition 2, Theorems 3–4, <https://doi.org/10.48550/arXiv.2110.11277>.
