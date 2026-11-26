# Basic reproduction number of the SEIRUC model with reported and unreported infectives

**Model.** The compartments are susceptible $S$, exposed $E$, symptomatic infectious $I$, reported infectious $R$, unreported infectious $U$ and confirmed (isolated) $C$. Infection is driven by contact with $I$, $R$ and $U$:

$$S' = \Lambda - \frac{\beta S}{N}(I+U+R) - \delta S,\qquad E' = \frac{\beta S}{N}(I+U+R) - \theta_1 E,\qquad I' = aE - \theta_2 I,$$

$$R' = \gamma q I - \theta_3 R + \eta U,\qquad U' = \gamma(1-q)I - \theta_4 U,\qquad C' = c_1E + c_2I + c_3R + c_4U - \delta_5 C,$$

with $\theta_1 = a+\delta_1+c_1$, $\theta_2 = \gamma+\delta_2+c_2$, $\theta_3 = \delta_3+c_3$ and $\theta_4 = \delta_4+c_4+\eta$. A fraction $q\in[0,1]$ of infectious individuals become reported, unreported cases are detected at rate $\eta$, and $c_k$ are the confirmation (isolation) rates. All parameters are positive.

**Theorem.**

1. Nonnegative data give nonnegative solutions. With $\mu = \min(\delta,\delta_1,\dots,\delta_5)$, the set $\{N \le \Lambda/\mu\}$ is positively invariant and attracting.
2. The next-generation matrix gives

$$\mathcal{R}_0 = \frac{a\beta\Lambda\,\mathcal{P}}{N\delta\,\theta_1\theta_2\theta_3\theta_4},\qquad \mathcal{P} = \gamma(1-q)(\eta+\theta_3) + \theta_4(\theta_3 + q\gamma) .$$

Here $N$ is treated as a fixed population size; at the disease-free state $S_0 = \Lambda/\delta$.
3. The disease-free equilibrium $(\Lambda/\delta,0,0,0,0,0)$ is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$.
4. A positive endemic equilibrium exists only when $\mathcal{R}_0 > 1$, with $S_* = \Lambda/(\delta\mathcal{R}_0)$ and every infected coordinate proportional to $\mathcal{R}_0 - 1$.

## Expansion

The factor $\mathcal{P}/(\theta_3\theta_4)$ can be read off from the expected time a new symptomatic case spends in the three infectious classes. Writing it as

$$\frac{\mathcal{P}}{\theta_3\theta_4} = 1 + \frac{\gamma q}{\theta_3} + \frac{\gamma(1-q)}{\theta_4} + \frac{\gamma(1-q)\eta}{\theta_3\theta_4},$$

the terms correspond to time spent in $I$, in $R$ after direct reporting, in $U$, and in $R$ after late detection from $U$. Each term is scaled by the mean time $1/\theta_2$ in $I$. With the factor $a/\theta_1$ for surviving the exposed stage unconfirmed, this gives $\mathcal{R}_0 = \beta(S_0/N)(a/\theta_1)(1/\theta_2)\,\mathcal{P}/(\theta_3\theta_4)$. This is the spectral radius of $FV^{-1}$, since $F$ has rank one. Raising any confirmation rate $c_k$ lowers $\mathcal{R}_0$. Local stability of the endemic state requires additional Routh–Hurwitz inequalities.

## Depends on

- [Basic reproduction number of the next-generation matrix](../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Sources

- P. Tamilalagan, B. Krithika and P. Manivannan, "A SEIRUC mathematical model for transmission dynamics of COVID-19", arXiv:2106.08327 (2021), Section 2 and Theorems 3.1–3.4, <https://doi.org/10.48550/arXiv.2106.08327>.
