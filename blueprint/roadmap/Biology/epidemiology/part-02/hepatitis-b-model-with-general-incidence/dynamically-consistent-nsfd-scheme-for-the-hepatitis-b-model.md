# Dynamically consistent NSFD scheme for the hepatitis B model

For the hepatitis B model $S' = \Lambda - f(S,I) - (\mu_0+\nu)S$, $I' = f(S,I) - (\mu_0+\mu_1+\beta)I$, $R' = \beta I + \nu S - \mu_0 R$ with incidence $f$ satisfying (H1)–(H5) of [the continuous model](global-threshold-dynamics-of-the-hepatitis-b-model-with-general-incidence.md), write $f(S,I) = S\,f^*(S,I)$. Let $\varphi(\Delta t) = \Delta t + O(\Delta t^2) > 0$ be a denominator function. The **nonstandard finite difference (NSFD) scheme** is

$$

\begin{aligned}
\frac{S_{n+1}-S_n}{\varphi(\Delta t)} &= \Lambda - S_{n+1} f^*(S_n,I_n) - (\mu_0+\nu)S_{n+1},\\
\frac{I_{n+1}-I_n}{\varphi(\Delta t)} &= S_{n+1} f^*(S_n,I_n) - (\mu_0+\mu_1+\beta)I_{n+1},\\
\frac{R_{n+1}-R_n}{\varphi(\Delta t)} &= \beta I_{n+1} + \nu S_{n+1} - \mu_0 R_{n+1},
\end{aligned}

$$

which is explicit: each line is linear in the new value.

**Theorem.** For every step size $\Delta t > 0$:

1. $\mathbb{R}_+^3$ is positively invariant and the discrete solutions satisfy the same asymptotic bounds as the ODE: $\limsup S_n \le \Lambda/(\mu_0+\nu)$, $\Lambda/p \le \limsup (S_n + I_n) \le \Lambda/q$ with $p = \max\{\mu_0+\nu,\mu_0+\mu_1+\beta\}$, $q = \min\{\mu_0+\nu,\mu_0+\mu_1+\beta\}$.
2. The scheme has exactly the equilibria of the ODE; the disease-free equilibrium is locally asymptotically stable if $\mathcal R_0 \le 1$ and unstable if $\mathcal R_0 > 1$, and the endemic equilibrium is locally asymptotically stable whenever $\mathcal R_0 > 1$.
3. The scheme converges with order $1$: there are constants $\tau, m > 0$ with $|S(t_n)-S_n| + |I(t_n)-I_n| + |R(t_n)-R_n| \le \frac{\tau\Delta t}{2m}\,(e^{m t_n}-1)$.

## Depends on

- [Global threshold dynamics of the hepatitis B model with general incidence](global-threshold-dynamics-of-the-hepatitis-b-model-with-general-incidence.md)

## Expansion

Solving each line for the new value gives $S_{n+1} = (S_n + \varphi\Lambda)/(1 + \varphi f^*(S_n,I_n) + \varphi(\mu_0+\nu))$, and similarly for $I_{n+1}$ and $R_{n+1}$; all are ratios of nonnegative quantities, which gives positivity for every step. Adding the first two lines yields a linear recursion for $S_n + I_n$ that is bounded between geometric sequences, giving the bounds. Local stability follows from the Jacobian of the map at the equilibria, using $f^*(S^0,0) = 0$, $\partial_I f^*(S^0,0) = \partial_I f(S^0,0)/S^0$ and the Jury conditions. Convergence of order one is the usual consistency-plus-stability argument, since $\varphi(\Delta t) = \Delta t + O(\Delta t^2)$.

## Sources

- Manh Tuan Hoang, "Dynamical analysis of a generalized hepatitis B epidemic model and its dynamically consistent discrete model", arXiv (2021). Section 3 (Theorems 4–6, Corollaries 1–2). <https://doi.org/10.48550/arXiv.2112.06284>. Published version: Mathematics and Computers in Simulation 205 (2023), 291–314, <https://doi.org/10.1016/j.matcom.2022.10.006>; locators above refer to the arXiv version.
