# Basic offspring number with phase-type biting dwell times

A **phase-type distribution** $\mathrm{PH}(\vec\alpha, A)$ is the absorption time of a continuous-time Markov chain with $n$ transient states, initial distribution $\vec\alpha$ over them and transient rate matrix $A$ ($a_{ij} \ge 0$ for $i \ne j$, $a_{jj} < 0$), with exit-rate vector $-A\vec 1$. Its mean is $\vec\alpha^{T}(-A)^{-1}\vec 1$, and phase-type laws are dense among distributions on $(0,\infty)$.

**Model.** Juveniles $J$, biting-stage adults $\vec B = (B_1, \dots, B_n)^T$, ovipositing adults $V$ and resting adults $R$ obey

$$\begin{aligned}
\dot J &= \varphi(V, J) - (\rho_J + \mu_J) J, &
\dot{\vec B} &= (\rho_J J + \gamma_R R)\,\vec\alpha + A^{T}\vec B - \mu \vec B,\\
\dot V &= -(A\vec 1)^{T}\vec B - (\gamma_V + \mu) V, &
\dot R &= \gamma_V V - (\gamma_R + \mu) R,
\end{aligned}$$

so the biting dwell time is $\mathrm{PH}(\vec\alpha, A)$ (linear chain trick). Here $\rho_J$ is maturation, $\mu_J, \mu$ are death rates, $\gamma_V, \gamma_R$ are the rates of leaving oviposition and rest, and the recruitment $\varphi(V,J)$ satisfies regularity assumptions with $\phi_V = \partial_V\varphi(0,0)$ and $\phi_J = \partial_J\varphi(0,0)$.

Define

$$\tau = \vec\alpha^{T}(\mu I - A)^{-1}(-A\vec 1), \qquad n_G = \left(1 - \tau\,\frac{\gamma_V}{\mu + \gamma_V}\,\frac{\gamma_R}{\mu + \gamma_R}\right)^{-1}.$$

Here $\tau$ is the probability of leaving the biting state alive, and $n_G$ is the expected number of gonotrophic cycles.

**Theorem.** With the **basic offspring number**

$$\mathcal N_0 = \tau \times \frac{\phi_V}{\mu + \gamma_V} \times \frac{\rho_J}{\rho_J + \mu_J - \phi_J} \times n_G,$$

the extinction equilibrium is locally asymptotically stable if and only if $\mathcal N_0 < 1$. For logistic recruitment $\varphi = \phi(1 - J/K_J)V$ there is a unique positive equilibrium exactly when $\mathcal N_0 > 1$. For linear recruitment $\varphi = \phi V$ a positive equilibrium exists only in the degenerate case $\mathcal N_0 = 1$.

## Expansion

The four factors follow one adult through a gonotrophic cycle: survive and complete blood-feeding ($\tau$, computed from the phase-type law of the minimum of the biting time and an $\mathrm{Exp}(\mu)$ death time, which is again phase-type with matrix $A - \mu I$); lay on average $\phi_V/(\mu + \gamma_V)$ eggs during oviposition; each egg survives to adulthood with probability $\rho_J/(\rho_J + \mu_J - \phi_J)$; and the cycle repeats a geometric number of times with mean $n_G$. The threshold comes from the next-generation matrix of the linearization at the origin. Choosing $(\vec\alpha, A)$ empirically from gonotrophic-cycle data, phenomenologically as an Erlang law, or mechanistically from host-seeking, probing and interruption stages changes $\tau$ and $n_G$ but not this formula. The same structure carries into the host–vector $R_0$, where multiple biting raises the contact rate but can lengthen the cycle and lower survival, so its effect on $R_0$ is not monotone.

## Sources

- K. J. Dahlin, M. A. Robert, L. M. Childs, "Once bitten, twice shy: a modeling framework for incorporating heterogeneous mosquito biting into transmission models", Bulletin of Mathematical Biology (2025), Eqs. (1)–(2), Proposition 1, Theorem 1 and Corollaries 1–2, <https://doi.org/10.1007/s11538-025-01540-z>, PMCID PMC12528224.
