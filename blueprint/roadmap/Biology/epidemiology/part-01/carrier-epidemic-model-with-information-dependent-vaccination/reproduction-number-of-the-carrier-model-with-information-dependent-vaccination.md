# Reproduction number of the carrier model with information-dependent vaccination

**Model.** For a disease with asymptomatic carriers (as in bacterial meningitis), split the population into susceptible $S$, vaccinated $V$, carriers $C$, infectious $I$ and recovered $R$, $N = S + V + C + I + R$, and let $M$ be an information index summarizing current and past prevalence. With exponentially fading memory of mean length $1/a$ and information proportional to prevalence, $M(t) = \int_{-\infty}^t k\, I(\tau)\, a e^{-a(t-\tau)}\, d\tau$, the linear chain trick gives

$$\begin{aligned}
\dot S &= \Lambda - \lambda S - (\nu_0 + bM) S + \phi R - \mu S, \\
\dot V &= (\nu_0 + bM) S - \mu V, \\
\dot C &= \lambda S - (\sigma + \delta + \mu) C, \\
\dot I &= \sigma C - (\rho + \mu + d) I, \\
\dot R &= \delta C + \rho I - (\phi + \mu) R, \\
\dot M &= a (k I - M),
\end{aligned} \qquad \lambda = \beta \frac{\epsilon C + I}{N},$$

with all parameters positive and $\epsilon \ge 1$ the extra infectiousness of carriers. Vaccination is lifelong; immunity after recovery wanes at rate $\phi$; the information-dependent vaccination rate is $\nu(M) = \nu_0 + bM$.

**Invariant region (Theorem 1).** With $\tilde N = \Lambda/\mu$, the set

$$\Omega = \Bigl\{(S, V, C, I, R, M) \in \mathbb R^6_+ : 0 \le M \le k \tilde N,\ \tilde N \tfrac{\mu}{\mu + d} \le S + V + C + I + R \le \tilde N\Bigr\}$$

is positively invariant and absorbing.

**Disease-free equilibrium and $\mathcal R_0$.** The disease-free equilibrium is $E_0 = (S_0, V_0, 0, 0, 0, 0)$ with $S_0 = \Lambda/(\mu + \nu_0)$ and $V_0 = \nu_0 \Lambda/(\mu(\mu + \nu_0))$. Taking $(C, I)$ as infected compartments, the next-generation matrix gives

$$\mathcal R_0 = \frac{\beta \mu}{(\mu + \nu_0)(\sigma + \delta + \mu)} \Bigl(\epsilon + \frac{\sigma}{\rho + \mu + d}\Bigr).$$

The behavioural parameters $b$, $k$ and $a$ do not enter $\mathcal R_0$: information-driven vaccination responds to prevalence that is zero at $E_0$, so only the baseline rate $\nu_0$ shifts the threshold.

## Expansion

Adding the first five equations gives $\dot N = \Lambda - \mu N - d I$, so $\Lambda - (\mu + d) N \le \dot N \le \Lambda - \mu N$, which traps $N$ between $\Lambda/(\mu + d)$ and $\Lambda/\mu$; the $M$ equation then bounds $M$ by $k \tilde N$. At $E_0$, $S_0/N_0 = \mu/(\mu + \nu_0)$, so the new-infection matrix is $F = \frac{\beta \mu}{\mu + \nu_0} \begin{pmatrix} \epsilon & 1 \\ 0 & 0 \end{pmatrix}$ and the transition matrix is $V = \begin{pmatrix} \sigma + \delta + \mu & 0 \\ -\sigma & \rho + \mu + d \end{pmatrix}$. Since $F V^{-1}$ has rank one, its spectral radius is its $(1,1)$ entry: a carrier generates $\epsilon \beta$ infections per unit time over a carrier period $1/(\sigma + \delta + \mu)$, plus, with probability $\sigma/(\sigma + \delta + \mu)$, $\beta$ per unit time over an infectious period $1/(\rho + \mu + d)$, all scaled by the susceptible fraction.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Sources

- B. Buonomo, A. d'Onofrio, S. M. Kassa, Y. H. Workineh, "Modeling the effects of information-dependent vaccination behavior on meningitis transmission", arXiv:2005.11823 (2020), Section 2 (the model) and Section 3 (Theorem 1, disease-free equilibrium and basic reproduction number). <https://doi.org/10.48550/arXiv.2005.11823>
