# A fully implicit θ-scheme preserves positivity and the extinction–persistence threshold of the stochastic SIS model

**Model.** In the stochastic SIS model of Gray et al., with population size $N$, transmission $\beta$, recovery $\gamma$, death rate $\mu$ and noise intensity $\sigma$ on the transmission rate, the number of infectives solves
$$dI = I\big[(\beta N - \mu - \gamma - \beta I)\,dt + \sigma(N - I)\,dW\big],\qquad I(0) \in (0,N),$$
and has the stochastic threshold
$$R_0^S = \frac{\beta N}{\mu+\gamma} - \frac{\sigma^2N^2}{2(\mu+\gamma)}:$$
the disease dies out if $R_0^S<1$ and persists if $R_0^S > 1$.

**Scheme.** With step $h$, a truncated Gaussian increment $\xi^h_n$ (bounded so the iterates stay in $[0,N]$) and weights $\theta, \vartheta \in [0,1]$, the fully implicit split-step method is
$$I^*_{n+1} = I_n + \theta h(\beta N-\mu-\gamma-\beta I_n)I^*_{n+1} + (1-\theta)h(\beta N-\mu-\gamma-\beta I_n)I_n,$$
$$I_{n+1} = I^*_{n+1} + \sqrt h\,\sigma\big[\vartheta I_n(N - I^*_{n+1}) + (1-\vartheta)I_n(N-I_n)\big]\xi^h_n ,$$
which is linear in the unknowns at each step ($\theta=\vartheta=0$: truncated forward Euler; $\theta=\vartheta=1$: truncated backward Euler).

**Theorems.**
1. There is $h_0 > 0$ such that for $0 < h < h_0$ the numerical solution is positive and bounded by $N$.
2. It converges in mean square to the exact solution on $[0,T]$ with order $1/2$.
3. *Extinction, small noise:* if $R_0^S < 1$ and $\sigma^2 < \beta/(2N)$, then for small $h$, $\limsup_n \frac{\log I_{n+1}}{(n+1)h} < 0$, so $I_n \to 0$ exponentially.
4. *Extinction, large noise:* if $\sigma^2 > \max\big\{\frac{\beta}{N}, \frac{\beta^2}{2(\mu+\gamma)}, \frac{\beta^2}{8(\mu+\gamma)-4\beta N}\big\}$, the same exponential extinction holds.
5. *Persistence:* if $R_0^S > 1$ and $\frac{3-\sqrt5}{4} \le \vartheta < \frac12$, then for small $h$ the iterates oscillate around an explicit positive level $\xi^+$: $\liminf_n I_{n+1} \le \xi^+ \le \limsup_n I_{n+1}$.

## Expansion

Treating the drift implicitly, but with the quadratic factor frozen at $I_n$, makes each step a linear equation with a positive solution for small $h$; the truncation of the Brownian increment keeps the diffusion step from pushing the iterate outside $[0,N]$. Mean-square convergence follows from the one-sided Lipschitz property of the drift and the global Lipschitz property of the diffusion on $[0,N]$. The extinction results mimic the continuous-time proof: a discrete Itô-type expansion of $\log I_{n+1}$ has drift approximately $(\beta N-\mu-\gamma) - \tfrac12\sigma^2 N^2 < 0$ when $R_0^S<1$ (with the small-noise restriction controlling the quadratic terms), and a strong-noise bound otherwise; persistence uses a recurrence argument for the averaged drift around $\xi^+$.

## Sources

- Zeyao Jin, Zhiming Li, Shenglong Chen, "Dynamic Properties of Numerical Solution for Stochastic Epidemic Models with a Fully Implicit Form", arXiv:2610.36924 (2026), equations (sis), (dI) and (In4) and the positivity, mean-square convergence, extinction and persistence theorems of the main text, <https://doi.org/10.48550/arXiv.2610.36924>.
