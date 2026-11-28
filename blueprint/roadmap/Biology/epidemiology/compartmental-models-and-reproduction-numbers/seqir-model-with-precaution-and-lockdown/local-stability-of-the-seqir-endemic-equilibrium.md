# Local stability of the SEQIR endemic equilibrium

For the system

$$\begin{aligned}
S' &= A - kSE + b_1 Q - dS - pMS, \\
E' &= kSE - (b_2 + \alpha + \sigma + d)E, \\
Q' &= b_2 E - (b_1 + c + d)Q, \\
I' &= \alpha E + cQ - (\eta + d + \delta)I, \\
R' &= \eta I + \sigma E - dR + pMS,
\end{aligned}$$

with $k = \beta(1-\rho_1)(1-\rho_2)$, where $A > 0$ is recruitment, $\beta > 0$ the transmission rate, $\rho_1, \rho_2 \in (0,1)$ the precaution fractions of susceptibles and exposed, $b_2, \alpha, \sigma > 0$ the rates from $E$ to quarantine, to hospitalized infection and to recovery, $b_1, c > 0$ the rates from $Q$ back to $S$ and on to $I$, $\eta > 0$ recovery, $d > 0$ natural and $\delta \ge 0$ disease mortality, and $pM \ge 0$ the removal rate of susceptibles by the lockdown policy. Hospitalized individuals ($I$) are isolated and do not transmit.

suppose $\mathcal R_0 = kA/((d+pM)K) > 1$, with $K = b_2 + \alpha + \sigma + d$ and $m = b_1 + c + d$, so that the [endemic equilibrium](basic-reproduction-number-and-endemic-equilibrium-of-the-seqir-model.md) $(S^*, E^*, Q^*, I^*, R^*)$ exists with $E^* > 0$. Then its characteristic polynomial factors as

$$(\lambda + d)\,(\lambda + \eta + d + \delta)\,\bigl(\lambda^3 + C_1\lambda^2 + C_2\lambda + C_3\bigr),$$

with $a = kE^* + d + pM$ and

$$C_1 = a + m, \qquad C_2 = am + kKE^*, \qquad C_3 = kE^*\,(Km - b_1b_2),$$

and $C_1, C_2, C_3 > 0$ and $C_1C_2 - C_3 > 0$. By the Routh–Hurwitz criterion the endemic equilibrium is locally asymptotically stable whenever it exists.

## Depends on

- [Basic reproduction number and endemic equilibrium of the SEQIR model](basic-reproduction-number-and-endemic-equilibrium-of-the-seqir-model.md)

## Proof depends on

- [Routh–Hurwitz criterion for cubic polynomials](../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Expansion

The $I$ and $R$ equations do not feed back into $(S, E, Q)$, so the Jacobian is block lower triangular, contributing eigenvalues $-(\eta + d + \delta)$ and $-d$. Using $kS^* = K$, the $(S, E, Q)$ block is

$$J_3 = \begin{pmatrix} -a & -K & b_1 \\ kE^* & 0 & 0 \\ 0 & b_2 & -m \end{pmatrix},$$

and expanding $\det(\lambda I - J_3)$ along its first row gives $\lambda(\lambda + a)(\lambda + m) + kKE^*(\lambda + m) - b_1b_2kE^*$, which is the stated cubic. Positivity of $C_3$ uses $Km - b_1b_2 = b_2(c+d) + (\alpha + \sigma + d)m > 0$, and

$$C_1C_2 - C_3 = am(a+m) + akKE^* + b_1b_2kE^* > 0 .$$

The source states the same factorization; its printed $C_1$ omits the term $kE^*$ contained in $a$, which does not affect the conclusion.

## Sources

- M. Mandal, S. Jana, S. K. Nandi, A. Khatua, S. Adak, T. K. Kar, "A model based study on the dynamics of COVID-19: Prediction and control", *Chaos, Solitons & Fractals* 136 (2020) 109889, Section 3.4, Theorem 3.4 and Equation (5), <https://doi.org/10.1016/j.chaos.2020.109889> (PMC7218394).
