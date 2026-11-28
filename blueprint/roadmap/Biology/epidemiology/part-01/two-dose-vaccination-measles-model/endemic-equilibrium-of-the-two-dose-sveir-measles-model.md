# Endemic equilibrium of the two-dose SVEIR measles model

**Setting.** Consider the two-dose SVEIR measles model with parameters $N, \mu, \eta, \rho, \sigma, \omega, \beta, \alpha, \gamma > 0$ and $\delta \ge 0$,

$$
\begin{aligned}
S' &= \mu N - \beta S I - (\eta + \mu) S + \rho V_1, &
V_1' &= \eta S - (\rho + \sigma + \mu) V_1, \\
V_2' &= \sigma V_1 - (\omega + \mu) V_2, &
E' &= \beta S I - (\alpha + \mu) E, \\
I' &= \alpha E - (\gamma + \delta + \mu) I, & &
\end{aligned}
$$

with $D = (\eta + \mu)(\rho + \sigma + \mu) - \rho\eta > 0$ and basic reproduction number $\mathcal R_0 = \alpha\beta S^0/\big((\alpha + \mu)(\gamma + \delta + \mu)\big)$, where $S^0 = \mu N (\rho + \sigma + \mu)/D$.

**Proposition (existence and form).** An equilibrium with $I > 0$ exists if and only if $\mathcal R_0 > 1$, and it is then unique:

$$
S^* = \frac{(\alpha + \mu)(\gamma + \delta + \mu)}{\alpha \beta} = \frac{S^0}{\mathcal R_0}, \qquad
V_1^* = \frac{\eta S^*}{\rho + \sigma + \mu}, \qquad
V_2^* = \frac{\sigma \eta S^*}{(\omega + \mu)(\rho + \sigma + \mu)},
$$

$$
I^* = \frac{(\mathcal R_0 - 1)\, D}{\beta\, (\rho + \sigma + \mu)}, \qquad
E^* = \frac{(\gamma + \delta + \mu)\, I^*}{\alpha} .
$$

**Characteristic polynomial.** At this equilibrium the Jacobian has the eigenvalue $-(\omega + \mu)$, and the remaining four eigenvalues are the roots of $\lambda^4 + a_3 \lambda^3 + a_2 \lambda^2 + a_1 \lambda + a_0$, where every $a_i$ is positive whenever $I^* > 0$, and in particular

$$
a_0 = \beta\, (\alpha + \mu)(\gamma + \delta + \mu)(\rho + \sigma + \mu)\, I^* , \qquad a_3 = \beta I^* + (\eta + \mu) + (\rho + \sigma + \mu) + (\alpha + \mu) + (\gamma + \delta + \mu).
$$

Positive coefficients are necessary for local asymptotic stability. The Routh–Hurwitz criterion for a quartic additionally requires $a_3 a_2 > a_1$ and $a_3 a_2 a_1 > a_1^2 + a_3^2 a_0$; the source asserts stability of the endemic equilibrium for $\mathcal R_0 > 1$ from coefficient positivity alone, without checking these inequalities.

## Depends on

- [Reproduction number and disease-free threshold of the two-dose SVEIR measles model](reproduction-number-and-disease-free-threshold-of-the-two-dose-sveir-measles-model.md)

## Expansion

At equilibrium the $I$ equation gives $\alpha E^* = (\gamma + \delta + \mu) I^*$ and the $E$ equation gives $\beta S^* I^* = (\alpha + \mu) E^*$; with $I^* > 0$ these force $S^* = (\alpha + \mu)(\gamma + \delta + \mu)/(\alpha\beta)$, which equals $S^0/\mathcal R_0$. The vaccine compartments follow linearly from $S^*$. Substituting $V_1^*$ into the $S$ equation and using $\mu N = S^0 D/(\rho + \sigma + \mu)$ yields

$$
\beta S^* I^* = \frac{(S^0 - S^*)\, D}{\rho + \sigma + \mu} = \frac{S^* (\mathcal R_0 - 1)\, D}{\rho + \sigma + \mu},
$$

so $I^* > 0$ exactly when $\mathcal R_0 > 1$. The coefficients of the quartic are obtained by expanding the reduced $4 \times 4$ Jacobian and simplifying with the equilibrium relation $\alpha\beta S^* = (\alpha + \mu)(\gamma + \delta + \mu)$.

## Sources

- M. A. Kuddus, M. Mohiuddin, A. Rahman, "Mathematical analysis of a measles transmission dynamics model in Bangladesh with double dose vaccination", Scientific Reports 11 (2021), 16571; endemic equilibrium Eq. (15), Lemma 2 and the characteristic polynomial Eqs. (16) and (17). <https://doi.org/10.1038/s41598-021-95913-8> (PMCID: PMC8368032).
