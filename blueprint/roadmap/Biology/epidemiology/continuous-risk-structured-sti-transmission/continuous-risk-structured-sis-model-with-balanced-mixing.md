# Continuous risk-structured SIS model of sexually transmitted infection with balanced mixing

**Model.** Let a sexually active population of steady size $N(r)$ be structured by risk $r \in [r_0, r_\infty]$, the number of partners per year, and split into susceptible $S(t,r)$ and infected $I(t,r)$. Individuals enter and leave by aging at rate $\mu$ and recover at rate $\gamma$ into susceptibility, as for chlamydia:

$$
\begin{aligned}
\partial_t S(t,r) &= \mu\big(N(r) - S(t,r)\big) - \lambda(t,r) S(t,r) + \gamma I(t,r), \\
\partial_t I(t,r) &= \lambda(t,r) S(t,r) - (\gamma + \mu) I(t,r),
\end{aligned}
\qquad
\lambda(t,r) = \int_{r_0}^{r_\infty} p(r,r')\,\beta(r,r')\,\frac{I(t,r')}{N(r')}\, dr' .
$$

**Balanced partnership and act numbers.** People of risk $r$ want a fraction $\rho(r,r')$ of their partners to have risk $r'$, mixing a random (proportional) component $\rho_{rm}(r,r') = r'N(r')/\int u N(u)\,du$ with a homophilous (biased) component. Desired partnership totals rarely satisfy the balance condition $N(r)p(r,r') = N(r')p(r',r)$. The actual number of partnerships is taken to be the harmonic mean of the two desires,

$$
P(r,r') = \frac{2\, r\rho(r,r')N(r)\cdot r'\rho(r',r)N(r')}{r\rho(r,r')N(r) + r'\rho(r',r)N(r')}, \qquad p(r,r') = \frac{P(r,r')}{N(r)},
$$

which is symmetric and lies closer to the smaller desire. Acts per partnership $A(r,r') = 2a(r)a(r')/(a(r) + a(r'))$, with $a(r) = A/r$, are balanced in the same way. Condom use $C(r,r')$ is either the harmonic mean of $c(r) = \alpha r/(c_0 + r)$ and $c(r')$ (the partner preferring less condom use decides) or one minus the harmonic mean of $1 - c$ (the partner preferring more condom use decides). The per-partner transmission probability $\beta(r,r')$ combines the per-act probabilities without and with a condom over the $A(r,r')$ acts.

**Basic reproduction number.** $\mathcal R_0$ is the spectral radius of the next-generation operator

$$
(K\phi)(r) = \int_{r_0}^{r_\infty} \tau\, p(r,r')\,\beta(r,r')\,\phi(r')\, dr', \qquad \tau = \frac{1}{\mu + \gamma},
$$

at the infection-free state. Partitioning $[r_0, r_\infty]$ into risk groups gives a next-generation matrix with entries $k_{ij} = \int_{r_{i-1}}^{r_i} \tau\, p(r_i, r_j)\, \beta(r_i, r_j)\, dr_j$, whose dominant eigenvalue approximates $\mathcal R_0$.

## Depends on

- [Basic reproduction number from the next-generation matrix](../../epidemiology/next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Any symmetric mean of $X(r,r') = r\rho(r,r')N(r)$ and $X(r',r)$ restores balance. The harmonic mean is chosen because a partnership needs both partners' consent, so the less willing side constrains the total. The same reasoning fixes acts and condom use per partnership. Since the integral kernel $\tau p\beta$ is nonnegative, Krein–Rutman theory makes $\mathcal R_0$ its dominant eigenvalue. The discretization reduces it to the Perron root of a nonnegative matrix, through which the effects of biased mixing and condom-use policies on early epidemic growth are compared.

## Sources

- Asma Azizi Boroojeni, "Mathematical Models for Predicting and Mitigating the Spread of Chlamydia Sexually Transmitted Infection", arXiv (2018). Chapter "Continuous Risk-based Model": model equations, partnership formation, probability of transmission per partner, basic reproduction number. <https://doi.org/10.48550/arXiv.1806.04754>
