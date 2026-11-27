# Reproduction number of a hepatitis B model with vaccination and chronic carriers

**Model.** The population is divided into susceptible $S$, acutely infected $A$, latent/immune-phase $M$, chronic carriers $C$, recovered $R$ and vaccinated $V$ individuals. With a variable-order Caputo difference operator $\Delta^{\alpha(t)}$, $0<\alpha(t)<1$ (the ordinary difference or derivative when $\alpha\equiv1$),

$$\begin{aligned}
\Delta^{\alpha(t)}S&=\delta d(1-rC)+wV-(\mu_1+\beta M+n\beta C+k)S,\\
\Delta^{\alpha(t)}A&=(\beta M+n\beta C)S-(\mu_1+\gamma)A,\\
\Delta^{\alpha(t)}M&=\gamma A+(\delta dr-\mu_1-\mu_2-a-m)M,\\
\Delta^{\alpha(t)}C&=aM-(e+\mu_1)C,\\
\Delta^{\alpha(t)}R&=mM+eC-\mu_1R,\\
\Delta^{\alpha(t)}V&=\delta(1-d)+kS-(\mu_1+w)V.
\end{aligned}$$

Here $\delta$ is recruitment, $d$ the unvaccinated fraction at birth, $r$ the probability of vertical transmission from carriers, $k$ the vaccination rate, $w$ the waning rate of vaccine immunity, $n$ the relative infectiousness of carriers, $\mu_1$ natural and $\mu_2$ disease-induced mortality.

**Theorem.** Under Lipschitz bounds on the right-hand sides, the system has a unique solution on $[0,T]$. Solutions starting in $\mathbb R_+^6$ remain in $\mathbb R_+^6$, and the total population satisfies $0<S+A+M+C+R+V<\delta/\mu_1$. By the next-generation method, the basic reproduction number is

$$\mathcal R_0=\frac{\delta\beta\gamma(\mu_1+e+na)(w+d\mu_1)}{\mu_1(\mu_1+\gamma)(\mu_1+e)(w+k+\mu_1)(\mu_1+\mu_2+a+m-r\delta d)},$$

and the disease-free equilibrium is locally asymptotically stable when $\mathcal R_0<1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

At the disease-free state the susceptible level is $S_0=\delta(w+d\mu_1)/\big(\mu_1(w+k+\mu_1)\big)$: vaccination at rate $k$ removes susceptibles, and waning at rate $w$ returns them. A new infection passes through the acute class with probability $\gamma/(\mu_1+\gamma)$. In the $M$ stage it infects at rate $\beta S_0$ for a mean time $1/(\mu_1+\mu_2+a+m-r\delta d)$; vertical transmission lengthens this effective time. With probability proportional to $a$ it moves on to the chronic stage, where it infects with relative strength $n$ for mean time $1/(\mu_1+e)$. Multiplying these factors gives $\mathcal R_0=\rho(FV^{-1})$. For variable-order discrete systems, local stability follows when all eigenvalues of the Jacobian at the equilibrium lie in the stability region of the fractional difference operator, which holds when $\mathcal R_0<1$. Raising $k$ or lowering $w$ reduces $\mathcal R_0$ through $S_0$.

## Sources

- Meriem Boukhobza, Amar Debbouche, Lingeshwaran Shangerganesh and Delfim F.M. Torres, "Modeling the dynamics of the Hepatitis B virus via a variable-order discrete system", *Chaos, Solitons & Fractals* 184 (2024), 114987, <https://doi.org/10.1016/j.chaos.2024.114987>. Preprint version: arXiv:2405.14887 (2024), Section 1 (model), Theorem 3.1 (existence and uniqueness), Theorems 3.2–3.3 (positivity and bound on total population), Section 4 ($\mathcal R_0$ by the next-generation matrix), Theorem 4.1 (local stability of the disease-free equilibrium), <https://doi.org/10.48550/arXiv.2405.14887>.
