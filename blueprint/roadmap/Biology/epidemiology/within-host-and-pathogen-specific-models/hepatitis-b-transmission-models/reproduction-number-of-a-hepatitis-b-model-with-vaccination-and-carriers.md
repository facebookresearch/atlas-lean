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

**Theorem.** Under Lipschitz bounds on the right-hand sides, the system has a unique solution on $[0,T]$. Assume $\mu_1+\mu_2+a+m > r\delta d$, so that the $M$ stage has a positive net exit rate. By the next-generation method, the basic reproduction number is

$$\mathcal R_0=\frac{\delta\beta\gamma(\mu_1+e+na)(w+d\mu_1)}{\mu_1(\mu_1+\gamma)(\mu_1+e)(w+k+\mu_1)(\mu_1+\mu_2+a+m-r\delta d)},$$

and the disease-free equilibrium is locally asymptotically stable when $\mathcal R_0<1$. The total population $B=S+A+M+C+R+V$ satisfies $\Delta^{\alpha(t)}B=\delta-\mu_1B-\mu_2M+\delta dr(M-C)$, so it obeys no bound $B<\delta/\mu_1$ in general: a bound of this kind needs $B(0)<\delta/\mu_1$ together with control of the vertical-transmission term $\delta drM$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

At the disease-free state the susceptible level is $S_0=\delta(w+d\mu_1)/\big(\mu_1(w+k+\mu_1)\big)$: vaccination at rate $k$ removes susceptibles, and waning at rate $w$ returns them. A new infection passes through the acute class with probability $\gamma/(\mu_1+\gamma)$. In the $M$ stage it infects at rate $\beta S_0$ for a mean time $1/(\mu_1+\mu_2+a+m-r\delta d)$; vertical transmission lengthens this effective time. Without the hypothesis $\mu_1+\mu_2+a+m>r\delta d$ the $M$-diagonal entry of the Jacobian at the disease-free state is nonnegative, the denominator of $\mathcal R_0$ is not positive, and $M$ can grow even though the formula gives $\mathcal R_0<1$. With probability proportional to $a$ it moves on to the chronic stage, where it infects with relative strength $n$ for mean time $1/(\mu_1+e)$. Multiplying these factors gives $\mathcal R_0=\rho(FV^{-1})$. For variable-order discrete systems, local stability follows when all eigenvalues of the Jacobian at the equilibrium lie in the stability region of the fractional difference operator, which holds when $\mathcal R_0<1$. Raising $k$ or lowering $w$ reduces $\mathcal R_0$ through $S_0$.

The page claims no positivity. The source's Theorem 3.2 states that solutions starting in $\mathbb R_+^6$ remain there, but its proof only checks the signs of the right-hand sides on the boundary of $\mathbb R_+^6$, a continuous-time argument. For the difference operator the first step is $S(t_1) = S(0) + c\,f_S(0)$ with $c > 0$, and with $S(0) = 1$, $M(0) = K/\beta$ and the other classes $0$ one has $f_S(0) = \delta d - \mu_1 - k - K$, so $S(t_1) < 0$ once $K > \delta d + 1/c$.

## Sources

- Meriem Boukhobza, Amar Debbouche, Lingeshwaran Shangerganesh and Delfim F.M. Torres, "Modeling the dynamics of the Hepatitis B virus via a variable-order discrete system", *Chaos, Solitons & Fractals* 184 (2024), 114987, <https://doi.org/10.1016/j.chaos.2024.114987>. Preprint version: arXiv:2405.14887 (2024), Section 1 (model), Theorem 3.1 (existence and uniqueness), Theorem 3.2 (positivity, not established for the difference operator and not used here), Section 4 ($\mathcal R_0$ by the next-generation matrix), Theorem 4.1 (local stability of the disease-free equilibrium), <https://doi.org/10.48550/arXiv.2405.14887>.
