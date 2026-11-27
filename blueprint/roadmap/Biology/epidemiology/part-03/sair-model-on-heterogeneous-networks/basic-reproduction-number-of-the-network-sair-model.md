# Basic reproduction number of the network SAIR model

**Model.** On an uncorrelated network with degree distribution $p(k)$ over degrees $k_1, \dots, k_n$ and mean degree $\langle k\rangle$, let $S_k, A_k, I_k, R_k$ be the fractions of degree-$k$ nodes that are susceptible, asymptomatically infected, symptomatically infected and removed, and

$$\Theta_A = \frac{1}{\langle k \rangle}\sum_{k'} k' p(k') A_{k'}, \qquad \Theta_I = \frac{1}{\langle k \rangle}\sum_{k'} k' p(k') I_{k'} .$$

With transmission rates $\beta_1$ (asymptomatic) and $\beta_2$ (symptomatic), probability $\alpha \in [0,1]$ that a new infection is asymptomatic, progression rate $m$ from $A$ to $I$ after a latent delay $\tau \ge 0$, and removal rates $\gamma_1, \gamma_2 > 0$,

$$\begin{aligned}
\dot S_k &= -k S_k(\beta_1\Theta_A + \beta_2 \Theta_I), \\
\dot A_k &= \alpha\, k S_k(\beta_1\Theta_A + \beta_2 \Theta_I) - m A_k(t-\tau) - \gamma_1 A_k, \\
\dot I_k &= (1-\alpha)\, k S_k(\beta_1\Theta_A + \beta_2 \Theta_I) + m A_k(t-\tau) - \gamma_2 I_k, \\
\dot R_k &= \gamma_1 A_k + \gamma_2 I_k .
\end{aligned}$$

**Proposition.** The basic reproduction number at the disease-free equilibrium $S_k \equiv 1$ is

$$R_0 = \left( \frac{\alpha\beta_1}{m + \gamma_1} + \frac{\alpha\, m\, \beta_2}{(m + \gamma_1)\gamma_2} + \frac{(1-\alpha)\beta_2}{\gamma_2} \right) \frac{\langle k^2 \rangle}{\langle k \rangle} .$$

The three terms are the expected transmissions per contact-weighted infection from the asymptomatic stage, from asymptomatic individuals who later become symptomatic, and from directly symptomatic infections. The disease-free equilibrium is unstable for every $\tau \ge 0$ when $R_0 > 1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
## Expansion

Let $P$ be the $n \times n$ matrix $P_{ij} = k_i k_j p(k_j)/\langle k\rangle$, which has rank one and unique non-zero eigenvalue $\operatorname{tr}P = \langle k^2\rangle/\langle k \rangle$. Ordering infected compartments as $(A_k)_k, (I_k)_k$, the new-infection and transition matrices are

$$F = \begin{pmatrix} \alpha\beta_1 P & \alpha\beta_2 P \\ (1-\alpha)\beta_1 P & (1-\alpha)\beta_2 P \end{pmatrix}, \qquad V = \begin{pmatrix} (m+\gamma_1) I_n & 0 \\ -m I_n & \gamma_2 I_n \end{pmatrix}$$

(the delay does not affect the next-generation matrix). Then $FV^{-1} = \big(\begin{smallmatrix}\alpha\\1-\alpha\end{smallmatrix}\big)\big(c_A,\ \beta_2/\gamma_2\big) \otimes P$ with $c_A = \beta_1/(m+\gamma_1) + m\beta_2/((m+\gamma_1)\gamma_2)$; both Kronecker factors have rank one, so $\rho(FV^{-1})$ is the product of their traces, $\big(\alpha c_A + (1-\alpha)\beta_2/\gamma_2\big)\langle k^2\rangle/\langle k\rangle$. Interventions act on the bracket (reducing $\beta_1, \beta_2$, raising $\gamma_2$ by isolation) or on the network factor (reducing contacts of high-degree nodes).

## Sources

- C. Liu, X. Wu, R. Niu, X. Wu, R. Fan, "A new SAIR model on complex networks for analysing the 2019 novel coronavirus (COVID-19)", Nonlinear Dynamics 101 (2020) 1777–1787, Section 2 (system 1, Table 1, next-generation matrices $F$ and $V$, $R_0$ Eq. 2, Theorem 1), <https://doi.org/10.1007/s11071-020-05704-5> (PMC7299147).
