# Strain-specific reproduction numbers under one-way mutation in the vector

**Model.** Mosquitoes are recruited at rate $\lambda_M$, die at rate $\mu_M$, and are susceptible ($S_M$), exposed ($E_{M1}, E_{M2}$) or infectious ($I_{M1}, I_{M2}$) with the non-mutant strain $1$ or the mutant strain $2$. Humans are recruited at rate $\lambda_H$, die at rate $\mu_H$, and are susceptible, exposed ($E_{Hj}$), infectious asymptomatic ($I^N_{Hj}$) or symptomatic ($I_{Hj}$), then recovered. With biting rate $b$ and per-bite transmission probabilities $\beta_{HjM}$ (human to mosquito) and $\beta_{MjH}$ (mosquito to human), new mosquito infections with strain $j$ occur at rate $b\beta_{HjM} S_M (I^N_{Hj} + I_{Hj})/N_H$ and new human infections at rate $b\beta_{MjH} S_H I_{Mj}/N_H$. Exposed mosquitoes become infectious at rate $\gamma_{Mj}$; exposed humans become infectious at rate $\gamma_H$, a fraction $\varphi$ symptomatically, and recover at rate $q$. The strain mutates only in mosquitoes, irreversibly, at rate $\delta$: $E_{M1} \to E_{M2}$ and $I_{M1} \to I_{M2}$. The disease-free equilibrium is $S_M = \lambda_M/\mu_M$, $S_H = N_H = \lambda_H/\mu_H$.

**Theorem.** The next-generation matrix $FV^{-1}$ has characteristic polynomial $\lambda^6(\lambda^2 - \mathcal R_{02}^2)(\lambda^2 - \mathcal R_{01}^2)$, so $\mathcal R_0 = \max\{\mathcal R_{01}, \mathcal R_{02}\}$ with

$$\mathcal R_{01} = \sqrt{\frac{b^2 \beta_{H1M}\beta_{M1H}\, \gamma_H \gamma_{M1}\, \lambda_M \mu_H}{\lambda_H \mu_M (\delta + \mu_M)(q + \mu_H)(\gamma_H + \mu_H)(\delta + \gamma_{M1} + \mu_M)}},$$

$$\mathcal R_{02} = \sqrt{\frac{b^2 \beta_{H2M}\beta_{M2H}\, \gamma_H \gamma_{M2}\, \lambda_M \mu_H}{\lambda_H \mu_M^2 (q + \mu_H)(\gamma_H + \mu_H)(\gamma_{M2} + \mu_M)}}.$$

The disease-free equilibrium is locally asymptotically stable if $\mathcal R_0 < 1$ and unstable if $\mathcal R_0 > 1$. If $\mathcal R_{02} > 1$ an equilibrium with only the mutant strain exists. In the case $\delta = 0$ without mutation, if $\mathcal R_{01} > 1$ an equilibrium with only the non-mutant strain exists. For $\delta > 0$ no equilibrium carries strain $1$ alone: at such a point $E_{M1} > 0$ and $E_{M2} = 0$ give $dE_{M2}/dt \ge \delta E_{M1} > 0$. (The source's Theorem 2.1 asserts the non-mutant boundary equilibrium for every $\delta$, ignoring the $\delta$ terms of its system (1).) $\mathcal R_{01}$ decreases in the mutation rate $\delta$ while $\mathcal R_{02}$ does not depend on it.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Because mutation feeds strain-1 mosquitoes into strain-2 compartments but never back, $V$ is block lower triangular and $FV^{-1}$ has an upper-triangular block structure whose diagonal blocks are the two host–vector cycles; each cycle's $2 \times 2$ product gives $\mathcal R_{0j}^2$, the product of the mosquito-to-human and human-to-mosquito reproduction numbers, hence the square roots. Mutation acts on strain $1$ as extra removal at rate $\delta$ from both mosquito stages. Numerically, increasing $\delta$ can switch the dominant strain from non-mutant to mutant or produce coexistence, depending on the relative infectivities.

## Sources

- X. Feng, X. Huo, B. Tang, S. Tang, K. Wang and J. Wu, "Modelling and Analyzing Virus Mutation Dynamics of Chikungunya Outbreaks", *Scientific Reports* (2019), Methods, system (1), next-generation matrix computation (Eq. 2) and Theorem 2.1. <https://doi.org/10.1038/s41598-019-38792-4> (PMC6393467)
