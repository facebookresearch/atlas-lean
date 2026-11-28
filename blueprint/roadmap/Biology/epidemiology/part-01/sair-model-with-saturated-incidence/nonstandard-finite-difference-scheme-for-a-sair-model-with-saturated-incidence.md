# Nonstandard finite-difference scheme for a SAIR model with saturated incidence

Let $S, A, I, R \ge 0$ be the susceptible, asymptomatic, symptomatic infected and recovered (or quarantined) fractions of a population with equal birth and death rate $\mu > 0$, and consider

$$\begin{aligned}
S' &= \mu - \frac{\beta_0 S I}{1 + \alpha I^2} - \mu S, &
A' &= \frac{\beta_0 S I}{1 + \alpha I^2} - (\sigma + \delta + \epsilon + \mu)A,\\
I' &= \sigma A - (r + d + \mu)I, &
R' &= rI + \epsilon A - \mu R,
\end{aligned}$$

with positive parameters: transmission rate $\beta_0$, saturation constant $\alpha$, progression rate $\sigma$, disease mortality $\delta$ and $d$ of asymptomatic and symptomatic individuals, asymptomatic recovery rate $\epsilon$, and treatment or quarantine rate $r$. Its basic reproduction number is

$$R_0 = \frac{\beta_0\,\sigma}{(\sigma + \delta + \epsilon + \mu)(r + d + \mu)}.$$

With step $\tau > 0$ and denominator function $h = 1 - e^{-\tau}$, the nonstandard (Mickens-type) explicit scheme, in its deterministic form, is

$$\begin{aligned}
S^{n+1} &= \frac{S^n + h\mu}{1 + h\mu + \dfrac{h\beta_0 I^n}{1 + \alpha (I^n)^2}}, &
A^{n+1} &= \frac{A^n + \dfrac{h\beta_0 S^n I^n}{1 + \alpha (I^n)^2}}{1 + h(\sigma + \delta + \epsilon + \mu)},\\
I^{n+1} &= \frac{I^n + h\sigma A^n}{1 + h(r + d + \mu)}, &
R^{n+1} &= \frac{R^n + h r I^n + h\epsilon A^n}{1 + h\mu};
\end{aligned}$$

the stochastic version replaces $\beta_0$ by $\beta_0 + \sigma_1\Delta W_n$ with Brownian increments $\Delta W_n$.

1. **Positivity.** For positive initial data the deterministic scheme has a unique solution, and all iterates are positive for every step size.
2. **Equilibria.** The scheme has exactly the same disease-free and endemic equilibria as the continuous model.

The source's scheme (2.10) and map (3.6) print the $A$-denominator as $1 + h(\sigma + \delta\epsilon + \mu)$; the page writes $1 + h(\sigma + \delta + \epsilon + \mu)$, the loss rate of the continuous $A$-equation, because only with it does the fixed-point equation of the $A$-update, $(\sigma + \delta + \epsilon + \mu)A = \beta_0 SI/(1 + \alpha I^2)$, reproduce the model's equilibria as item 2 and the source's own equilibrium analysis require. The source also claims that the scheme keeps the total $S^n + A^n + I^n + R^n$ at most $1$ and that its equilibria are stable. Neither holds in general for this scheme: with $\tau = \ln 2$ ($h = 1/2$), $\mu = 1/2$, $\beta_0 = 20$, $\alpha = 0.01$, $\sigma = 1$, $\delta = \epsilon = r = d = 0.01$ and $(S, A, I, R)^0 = (1/2, 0, 1/2, 0)$, one step gives a total of about $1.94$, and the disease-free equilibrium is unstable whenever $R_0 > 1$.

Classical Euler, Runge–Kutta and Euler–Maruyama discretizations of the same model can produce negative or unbounded values at moderate step sizes.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Each update is a ratio of sums of nonnegative terms, because loss terms are evaluated implicitly in the denominator and gain terms explicitly in the numerator, so positivity holds by induction regardless of $\tau$. At a fixed point, $X^{n+1} = X^n$ turns each update into the corresponding steady-state equation of the ODE, so the equilibria coincide. $R_0$ comes from the next-generation matrix of the infected compartments $(A, I)$ at the disease-free state $S = 1$: new infections enter $A$ at rate $\beta_0$ per infected, and the product of the probability $\sigma/(\sigma + \delta + \epsilon + \mu)$ of progressing to $I$ and the mean infectious period $1/(r + d + \mu)$ gives the formula.

## Sources

- J. E. Macías-Díaz, A. Raza, N. Ahmed and M. Rafiq, "Analysis of a nonstandard computer method to simulate a nonlinear stochastic epidemiological model of coronavirus-like diseases", *Computer Methods and Programs in Biomedicine* (2021), Section 1, Eqs. (1.1)–(1.5) and Theorem 1; Section 2.4, Eq. (2.10); Section 3, Theorems 2–4, Lemma 5 and Theorem 6. <https://doi.org/10.1016/j.cmpb.2021.106054> (PMC8714259)
