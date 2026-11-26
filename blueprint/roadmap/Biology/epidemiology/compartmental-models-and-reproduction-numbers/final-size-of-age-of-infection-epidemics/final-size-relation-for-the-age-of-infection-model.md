# Final-size relation for the age-of-infection epidemic model

In a closed population of constant size $N$, let each individual make $a > 0$ contacts per unit time sufficient to transmit, and let $A(s) \ge 0$ be the mean infectivity of an individual at infection age $s$, with $\int_0^\infty A(s)\, ds < \infty$. The age-of-infection (Kermack–McKendrick) model for the number of susceptibles $S(t)$ is

$$S'(t) = -\frac{a}{N} S(t) \varphi(t), \qquad \varphi(t) = \int_0^\infty A(s)\,\bigl[-S'(t - s)\bigr]\, ds,$$

where $\varphi(t)$ is the total infectivity at time $t$. Its basic reproduction number is

$$\mathcal{R}_0 = a \int_0^\infty A(s)\, ds,$$

and if $S(t) \to S_0$ as $t \to -\infty$ and $S(t) \to S_\infty$ as $t \to \infty$, then

$$\log \frac{S_0}{S_\infty} = \frac{\mathcal{R}_0}{N}\bigl(S_0 - S_\infty\bigr),$$

which for an epidemic started by a vanishing number of infectives in a fully susceptible population ($S_0 = N$) is $\log(N/S_\infty) = \mathcal{R}_0 (1 - S_\infty/N)$.

## Depends on

- [Final-size relation (Kermack–McKendrick 1927)](../../kermack-mckendrick-sir-model/final-size.md)

## Expansion

Divide the equation by $S$ and integrate over the whole real line: $\log(S_0/S_\infty) = (a/N) \int_{-\infty}^{\infty} \varphi(t)\, dt$. By Fubini, $\int \varphi = \int_0^\infty A(s)\, ds \int_{-\infty}^\infty [-S'(t-s)]\, dt = (\mathcal{R}_0/a)(S_0 - S_\infty)$, which gives the relation. Nothing about the shape of $A$ enters, so the same final size holds for arbitrary distributions of time spent in latent and infectious stages, and for arbitrary sequences of infective compartments (for example with treatment, quarantine or isolation); with $A(s) = e^{-\gamma s}$ the model reduces to the SIR model with $\mathcal{R}_0 = a/\gamma$ and the relation becomes the classical Kermack–McKendrick final-size equation. The duration distribution matters for the epidemic's speed and peak, not for its final size.

## Sources

- Brauer F. Mathematical epidemiology: past, present, and future. *Infectious Disease Modelling* 2:113–127 (2017), Section 5.1, "The infection age epidemic model", equations (4) and (5). DOI <https://doi.org/10.1016/j.idm.2017.02.001>. PMCID PMC6001967.
