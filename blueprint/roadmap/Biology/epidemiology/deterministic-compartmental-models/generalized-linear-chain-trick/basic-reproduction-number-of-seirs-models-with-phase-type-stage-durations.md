# Basic reproduction number of SEIRS models with phase-type stage durations

**Model.** Let the latent period (state E), the infectious period (state I) and the duration of immunity (state R) be phase-type distributed with parameters $(\boldsymbol\alpha_E, \mathbf A_E)$, $(\boldsymbol\alpha_I, \mathbf A_I)$ and $(\boldsymbol\alpha_R, \mathbf A_R)$, of sizes $k_E, k_I, k_R$, and let all individuals die at rate $\mu > 0$. With sub-state vectors $\mathbf x$ (exposed), $\mathbf y$ (infectious) and $\mathbf z$ (recovered), the generalized linear chain trick gives the mean-field SEIRS model

$$\begin{aligned}
\dot S &= \Lambda(S,\mathbf x,\mathbf y,\mathbf z) - \mu S - \lambda(t) S + \bigl(-\mathbf 1^{\mathsf T}\mathbf A_R^{\mathsf T}\mathbf z\bigr),\\
\dot{\mathbf x} &= \boldsymbol\alpha_E\, \lambda(t) S + \mathbf A_E^{\mathsf T}\mathbf x - \mu\mathbf x,\\
\dot{\mathbf y} &= \boldsymbol\alpha_I\bigl(-\mathbf 1^{\mathsf T}\mathbf A_E^{\mathsf T}\mathbf x\bigr) + \mathbf A_I^{\mathsf T}\mathbf y - \mu\mathbf y,\\
\dot{\mathbf z} &= \boldsymbol\alpha_R\bigl(-\mathbf 1^{\mathsf T}\mathbf A_I^{\mathsf T}\mathbf y\bigr) + \mathbf A_R^{\mathsf T}\mathbf z - \mu\mathbf z,
\end{aligned}$$

with force of infection $\lambda(t) = \boldsymbol\beta^{\mathsf T}\mathbf y$ (stage-specific transmission rates $\boldsymbol\beta \in \mathbb R_{\ge 0}^{k_I}$) and a smooth birth term $\Lambda \ge 0$ for which the disease-free equilibrium $(S_0, \mathbf 0, \mathbf 0, \mathbf 0)$ is locally asymptotically stable without the pathogen. Put $\mathbf G_E = \mathbf A_E - \mu\mathbf I$ and $\mathbf G_I = \mathbf A_I - \mu\mathbf I$.

**Theorem.** The disease-free equilibrium is locally asymptotically stable if $\mathcal R_0 < 1$ and unstable if $\mathcal R_0 > 1$, where

$$\mathcal R_0 = \underbrace{\boldsymbol\alpha_I^{\mathsf T}\bigl(-\mathbf G_I^{-1}\bigr)(\boldsymbol\beta S_0)}_{\mathcal R_{0,\mathrm{new}}} \cdot \underbrace{\boldsymbol\alpha_E \cdot \bigl((-\mathbf G_E^{-1})(-\mathbf A_E\mathbf 1)\bigr)}_{\mathcal P_{E\to I}}.$$

Here $\mathcal R_{0,\mathrm{new}}$ is the expected number of infections caused by one infectious individual over its infectious period cut short by death, i.e. the expected reward with rates $\boldsymbol\beta S_0$ accumulated by the phase-type law that is the minimum of the infectious period and an $\mathrm{Exp}(\mu)$ lifetime, and $\mathcal P_{E\to I}$ is the probability of leaving E into I rather than dying.

**Corollary (Erlang stages).** With constant birth rate, Erlang latent and infectious periods of means $\tau_E, \tau_I$ and integer shapes $k_E, k_I \ge 1$ (rates $r_E = k_E/\tau_E$, $r_I = k_I/\tau_I$), homogeneous transmission $\boldsymbol\beta = \beta\mathbf 1$ and exponential immunity,

$$\mathcal R_0 = \beta S_0 \left(\sum_{j=0}^{k_I - 1} \frac{r_I^{\,j}}{(r_I + \mu)^{j+1}}\right) \left(\frac{r_E}{r_E + \mu}\right)^{k_E}.$$

The bracket is the mean of the Coxian time $\min(\text{infectious period}, \text{lifetime})$, and the last factor the probability of surviving all $k_E$ latent stages.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [Generalized linear chain trick for phase-type dwell times](generalized-linear-chain-trick-for-phase-type-dwell-times.md)

## Proof sketch

Apply the next-generation construction of van den Driessche and Watmough with infected compartments $(\mathbf x, \mathbf y)$. New infections enter only through $\mathbf x$, so $\mathbf F$ has the single nonzero block $\boldsymbol\alpha_E\boldsymbol\beta^{\mathsf T} S_0$, while $\mathbf V$ is block lower triangular with diagonal blocks $-\mathbf G_E^{\mathsf T}$, $-\mathbf G_I^{\mathsf T}$. Inverting $\mathbf V$ blockwise makes $\mathbf F\mathbf V^{-1}$ block upper triangular with a single nonzero diagonal block of rank one, so its spectral radius is a scalar product that factors into the expected-reward term for I and the absorption probability into I for E, both standard phase-type quantities. In the Erlang case the infectious time with mortality is Coxian with rates $r_I + \mu$ and continuation probabilities $r_I/(r_I + \mu)$, whose mean gives the finite geometric-type sum; this proves, for arbitrary $k_E, k_I$, a formula that had been conjectured. The same method gives a predator invasion threshold $\mathcal R_{\mathrm{pred}}$ for predator-prey models with phase-type maturation and lifetime.

## Sources

- Paul J. Hurtado and Cameron Richards, "Finding Reproduction Numbers for Epidemic Models and Predator-Prey Models of Arbitrary Finite Dimension Using the Generalized Linear Chain Trick", *Bulletin of Mathematical Biology* 87 (2025), 89, <https://doi.org/10.1007/s11538-025-01467-5>. Preprint version: arXiv:2008.06768 (2020), Theorem 3 (Section 3.1), Theorem 4 (Section 3.2), Corollary 2 (Section 3.3), Theorems 5 and 6, <https://doi.org/10.48550/arXiv.2008.06768>.
