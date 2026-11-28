# Functional limit theorems for SIS-type epidemics with varying infectivity and gradual waning immunity

**Model.** A closed population of $N$ individuals. After its $i$-th infection, individual $k$ has a random infectivity function $\lambda_{k,i}(\cdot)$ and a random susceptibility function $\gamma_{k,i}(\cdot)$ of the time elapsed since that infection; the pairs $(\lambda_{k,i}, \gamma_{k,i})_{i \ge 1}$ are i.i.d. across $k$ and $i$ (with separate i.i.d. initial pairs $(\lambda_{k,0}, \gamma_{k,0})$). Assume $0 \le \lambda_{k,i} \le \lambda_*$, $0 \le \gamma_{k,i} \le 1$, and that infectivity ends before susceptibility starts: $\sup\{t : \lambda_{k,i}(t) > 0\} \le \inf\{t : \gamma_{k,i}(t) > 0\}$, the infectious period being $\eta_{k,i}$. Write $\Upsilon_k^N(t)$ and $\Lambda^N_k(t)$ for the current susceptibility and infectivity of individual $k$. The force of infection and the mean susceptibility are

$$\overline{\mathfrak F}^N(t) = \frac1N\sum_{k=1}^N \Lambda^N_k(t), \qquad \overline{\mathfrak S}^N(t) = \frac1N\sum_{k=1}^N \Upsilon^N_k(t),$$

and individual $k$ is infected at rate $\Upsilon^N_k(t)\,\overline{\mathfrak F}^N(t)$. A typical example is $\lambda(t) = \lambda\mathbf 1\{t < \eta\}$ with $\gamma(t) = (1 - e^{-(t-\eta)})\mathbf 1\{t \ge \eta\}$: reinfection is possible and immunity wanes gradually.

**FLLN.** With $\bar\lambda(t) = \mathbb{E}[\lambda_{1,1}(t)]$, $\bar\lambda_0$ the analogous initial mean, and $\gamma,\gamma_0$ generic copies, $(\overline{\mathfrak S}^N, \overline{\mathfrak F}^N) \to (\overline{\mathfrak S}, \overline{\mathfrak F})$ in probability in $D^2$, where

$$\overline{\mathfrak S}(t) = \mathbb{E}\Big[\gamma_0(t)e^{-\int_0^t \gamma_0(r)\overline{\mathfrak F}(r)dr}\Big] + \int_0^t \mathbb{E}\Big[\gamma(t-s)e^{-\int_s^t\gamma(r-s)\overline{\mathfrak F}(r)dr}\Big]\overline{\mathfrak S}(s)\overline{\mathfrak F}(s)\,ds,$$

$$\overline{\mathfrak F}(t) = \bar I(0)\bar\lambda_0(t) + \int_0^t \bar\lambda(t-s)\overline{\mathfrak S}(s)\overline{\mathfrak F}(s)\,ds,$$

and the proportions of infected and uninfected individuals converge to explicit functionals of this solution. Moments converge at rate $\mathbb{E}|\overline{\mathfrak F}^N(t) - \overline{\mathfrak F}(t)|^k \le C_{k,T} N^{-k/2}$ and the convergence also holds almost surely for each $t$.

**FCLT.** Assume in addition that $\lambda$ and $\gamma$ are piecewise continuous with finitely many random breakpoints, $\lambda=\sum_{j\le\ell}\lambda^j\mathbf 1_{[\xi^{j-1},\xi^j)}$ and $\gamma=\sum_{j\le\ell}\gamma^j\mathbf 1_{[\zeta^{j-1},\zeta^j)}$ with continuous random pieces sharing, on each $[0,T]$, a deterministic modulus of continuity $\varphi_T\le Ct^{\alpha}$ with $\alpha>1/2$; that the c.d.f.s of the breakpoints $\xi^j,\zeta^j$ are $\rho$-Hölder with $\rho>1/2$; and the Hölder-type moment bounds $\mathbb{E}[(\lambda(t)-\lambda(s))^2] \le (\phi_1(t)-\phi_1(s))^{\alpha_1}$ and $\mathbb{E}[(\lambda(t)-\lambda(u))^2(\lambda(u)-\lambda(s))^2] \le (\psi_1(t)-\psi_1(s))^{\beta_1}$ for $s < u < t$, with $\alpha_1 > 1/2$, $\beta_1 > 1$, nondecreasing continuous $\phi_1,\psi_1$, and the same for $\gamma$. Then the fluctuations

$$\big(\hat{\mathfrak S}^N, \hat{\mathfrak F}^N\big) = \sqrt N\big(\overline{\mathfrak S}^N - \overline{\mathfrak S},\ \overline{\mathfrak F}^N - \overline{\mathfrak F}\big) \Rightarrow \big(\hat{\mathfrak S}, \hat{\mathfrak F}\big) \quad \text{in } D^2,$$

the unique continuous solution of a linear system of stochastic Volterra integral equations, obtained by linearizing the two FLLN equations around $(\overline{\mathfrak S}, \overline{\mathfrak F})$ and adding centered Gaussian driving processes that come from the randomness of the initial condition, of the infection times, and of the individual curves $(\lambda, \gamma)$. The rescaled numbers of infected and uninfected individuals converge jointly to Gaussian limits given by linear functionals of $(\hat{\mathfrak S}, \hat{\mathfrak F})$.

## Expansion

Coupling each individual to an independent copy driven by the deterministic force of infection $\overline{\mathfrak F}$ gives the $N^{-1/2}$ moment bounds; the FLLN is the resulting renewal-type system in which the susceptibility at time $t$ averages the waning curve over the time since the last infection. For the FCLT the fluctuation decomposes into a martingale part from Poisson infection clocks, a part from i.i.d. random curves (a functional CLT in $D$ needing the Hölder moment conditions for tightness), and a feedback part linear in $(\hat{\mathfrak S}, \hat{\mathfrak F})$. Because $\gamma$ is nonzero after recovery, a recovered individual's exposure integral $\int\gamma\,\overline{\mathfrak F}$ re-enters the equations, the feature that distinguishes this from SIR-type FCLTs.

## Sources

- Arsene-Brice Zotsa-Ngoufack, "Functional Central Limit Theorems for epidemic models with varying infectivity and waning immunity", ESAIM: Probability and Statistics 29 (2025), 45–112, <https://doi.org/10.1051/ps/2024015>; numbering as in arXiv:2311.02260: Section 2 (Assumptions 2.1 and 2.4–2.6), Theorem 2.2, Theorem 2.10, Corollary 2.11, Proposition 4.8 and Corollary 4.11.
