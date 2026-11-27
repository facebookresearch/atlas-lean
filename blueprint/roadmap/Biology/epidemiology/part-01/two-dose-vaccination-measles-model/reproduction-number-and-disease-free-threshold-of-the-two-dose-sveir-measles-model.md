# Reproduction number and disease-free threshold of the two-dose SVEIR measles model

**Model.** A population of fixed size $N > 0$ is split into susceptible $S$, first-dose vaccinated $V_1$, second-dose vaccinated $V_2$, exposed $E$, infectious $I$ and recovered $R$ individuals. With natural death and birth rate $\mu > 0$, first-dose rate $\eta > 0$, waning of first-dose protection $\rho \ge 0$, second-dose rate $\sigma > 0$, second-dose transfer to immunity $\omega > 0$, transmission rate $\beta > 0$, progression rate $\alpha > 0$, recovery rate $\gamma > 0$ and disease death rate $\delta \ge 0$, the infection-relevant subsystem is

$$
\begin{aligned}
S' &= \mu N - \beta S I - (\eta + \mu) S + \rho V_1, &
V_1' &= \eta S - (\rho + \sigma + \mu) V_1, \\
V_2' &= \sigma V_1 - (\omega + \mu) V_2, &
E' &= \beta S I - (\alpha + \mu) E, \\
I' &= \alpha E - (\gamma + \delta + \mu) I, & &
\end{aligned}
$$

with $R' = \gamma I + \omega V_2 - \mu R$ decoupled, on the region $\{(S, V_1, V_2, E, I) \in \mathbb{R}_{\ge 0}^5 : S + V_1 + V_2 + E + I \le N\}$.

**Disease-free equilibrium.** Put $D = (\eta + \mu)(\rho + \sigma + \mu) - \rho\eta = \eta(\sigma + \mu) + \mu(\rho + \sigma + \mu) > 0$. The unique equilibrium with $E = I = 0$ is

$$
S^0 = \frac{\mu N (\rho + \sigma + \mu)}{D}, \qquad V_1^0 = \frac{\mu \eta N}{D}, \qquad V_2^0 = \frac{\mu \eta \sigma N}{(\omega + \mu) D}, \qquad E^0 = I^0 = 0 .
$$

**Reproduction number.** With new infections $\mathcal F = \begin{pmatrix} 0 & \beta S^0 \\ 0 & 0 \end{pmatrix}$ and transitions $\mathcal V = \begin{pmatrix} \alpha + \mu & 0 \\ -\alpha & \gamma + \delta + \mu \end{pmatrix}$ on $(E, I)$, the spectral radius of $\mathcal F \mathcal V^{-1}$ is

$$
\mathcal R_0 = \frac{\alpha \beta S^0}{(\alpha + \mu)(\gamma + \delta + \mu)} = \frac{\alpha \beta \mu N (\rho + \sigma + \mu)}{(\alpha + \mu)(\gamma + \delta + \mu)\,\big[(\eta + \mu)(\rho + \sigma + \mu) - \rho \eta\big]} .
$$

**Theorem.** The disease-free equilibrium is locally asymptotically stable if $\mathcal R_0 < 1$ and unstable if $\mathcal R_0 > 1$.

Increasing either dose rate $\eta$ or $\sigma$ lowers $S^0$ and hence $\mathcal R_0$. With the parameters fitted to measles case data in Bangladesh for 2000 to 2019, $\mathcal R_0 \approx 1.44$; the normalized sensitivity index of $\mathcal R_0$ with respect to $\beta$ is $1$, the largest in magnitude, and with respect to $\eta$ it is the second largest.

## Depends on

- [Next-generation matrix and the basic reproduction number](../../next-generation-matrix-and-the-basic-reproductio/README.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

The Jacobian at the disease-free equilibrium has the eigenvalue $-(\omega + \mu)$ from the $V_2$ column; removing that row and column leaves a block upper-triangular matrix with diagonal blocks

$$
A_1 = \begin{pmatrix} -(\eta + \mu) & \rho \\ \eta & -(\rho + \sigma + \mu) \end{pmatrix}, \qquad
A_4 = \begin{pmatrix} -(\alpha + \mu) & \beta S^0 \\ \alpha & -(\gamma + \delta + \mu) \end{pmatrix}.
$$

Both have negative trace; $\det A_1 = D > 0$ always, and $\det A_4 = (\alpha + \mu)(\gamma + \delta + \mu)(1 - \mathcal R_0)$, which is positive exactly when $\mathcal R_0 < 1$. A $2 \times 2$ matrix with negative trace is Hurwitz if and only if its determinant is positive, which gives both directions of the threshold. The disease-free susceptible level $S^0$ falls below $N$ because vaccination diverts the inflow into $V_1$ and $V_2$, so $\mathcal R_0$ is the unvaccinated value $\alpha\beta N/((\alpha+\mu)(\gamma+\delta+\mu))$ scaled by $S^0/N$.

## Sources

- M. A. Kuddus, M. Mohiuddin, A. Rahman, "Mathematical analysis of a measles transmission dynamics model in Bangladesh with double dose vaccination", Scientific Reports 11 (2021), 16571; model Eqs. (2) to (13), disease-free equilibrium and next-generation matrix in the Results section, Lemma 1, the estimate of $\mathcal R_0$ and the sensitivity table. <https://doi.org/10.1038/s41598-021-95913-8> (PMCID: PMC8368032).
