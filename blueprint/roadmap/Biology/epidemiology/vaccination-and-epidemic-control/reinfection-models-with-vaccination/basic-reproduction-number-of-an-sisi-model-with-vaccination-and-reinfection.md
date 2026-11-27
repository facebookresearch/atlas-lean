# Basic reproduction number of an SISI model with vaccination and reinfection

**Model.** Susceptibles $S$ become primary infections $I_1$. Recovery, or vaccination of a fraction $\upsilon$ of recruits, moves individuals to a partially protected class $S_1$, which can be reinfected into $I_2$ at a reduced rate factor $\delta\in[0,1]$. Both infected classes transmit equally:

$$\begin{aligned}
\dot S&=(1-\upsilon)\Lambda-\mu S-\beta S(I_1+I_2),\\
\dot I_1&=\beta S(I_1+I_2)-(\mu+\mu'+\alpha)I_1,\\
\dot S_1&=\upsilon\Lambda+\alpha(I_1+I_2)-\mu S_1-\delta\beta S_1(I_1+I_2),\\
\dot I_2&=\delta\beta S_1(I_1+I_2)-(\mu+\mu'+\alpha)I_2,
\end{aligned}$$

with recruitment $\Lambda$, natural mortality $\mu$, disease mortality $\mu'$ and recovery rate $\alpha$.

**Theorem.**

1. Solutions are bounded, and $\Omega=\{S+I_1+S_1+I_2\le\Lambda/\mu\}$ is positively invariant.
2. There is a unique disease-free equilibrium $e^{(0)}=\big((1-\upsilon)\Lambda/\mu,\,0,\,\upsilon\Lambda/\mu,\,0\big)$. It is locally asymptotically stable if $\mathcal R_0<1$ and unstable if $\mathcal R_0>1$, where

$$\mathcal R_0=\frac{\Lambda\beta\,(\delta\upsilon+1-\upsilon)}{\mu(\mu+\mu'+\alpha)} .$$

3. When $\mathcal R_0>1$ there is a unique positive endemic equilibrium $e^{(1)}$, given explicitly in terms of the total infected level $I^{(1)}=I_1^{(1)}+I_2^{(1)}$.

## Proof sketch

At the disease-free state an infective meets susceptibles of density $(1-\upsilon)\Lambda/\mu$ with full susceptibility and vaccinated individuals of density $\upsilon\Lambda/\mu$ with susceptibility $\delta$. It stays infectious for mean time $1/(\mu+\mu'+\alpha)$, which gives $\mathcal R_0$. The Jacobian at $e^{(0)}$ has eigenvalues $-\mu$ (twice), $-(\mu+\mu'+\alpha)$, and $\Lambda\beta(\delta\upsilon+1-\upsilon)/\mu-(\mu+\mu'+\alpha)$, whose sign is that of $\mathcal R_0-1$. Vaccination lowers $\mathcal R_0$ only through the factor $1-\upsilon(1-\delta)$. If vaccine protection against a new variant is weak ($\delta$ near $1$), accelerating vaccination alone cannot push $\mathcal R_0$ below $1$. The critical vaccination coverage is $\upsilon^*=\big(1-\mu(\mu+\mu'+\alpha)/(\Lambda\beta)\big)/(1-\delta)$, which exceeds $1$ when $\delta$ is close to $1$.

## Sources

- Benny Yong, Jonathan Hoseana and Livia Owen, "Combating new COVID-19 variants in Indonesia : Is accelerating four-dose vaccinations sufficient?", *Journal of Interdisciplinary Mathematics* 28 (2025), 2491–2517, <https://doi.org/10.47974/jim-1999>. Preprint version: arXiv:2309.00219 (2023), Section 2 (model), Theorem 1 (boundedness and invariant region), Theorem 2 with the formula for $\mathcal R_0$ (disease-free equilibrium), Theorem 3 (endemic equilibrium), <https://doi.org/10.48550/arXiv.2309.00219>.
