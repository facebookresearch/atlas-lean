# Basic reproduction number of the SARIIqSq model

**Model.** The population $N = S + S_q + A + I + I_q + R$ consists of susceptibles $S$, quarantined susceptibles $S_q$, asymptomatic (not yet symptomatic) infectives $A$, symptomatic infectives $I$, isolated infectives $I_q$ and recovered $R$. Contacts of symptomatic infectives occur at rate $\varepsilon_s$, each transmitting with probability $\beta_s$, with $0 < \beta_s \le 1$; a fraction $\rho_s$, with $0 \le \rho_s < 1$, of exposed contacts is traced. With inflow $\Lambda_s$ and natural death rate $\delta$,

$$\begin{aligned}
S' &= \Lambda_s - \big(\beta_s + \rho_s(1 - \beta_s)\big)\varepsilon_s \frac{S I}{N} - \delta S + m_s S_q, \\
S_q' &= (1 - \beta_s)\varepsilon_s\rho_s \frac{S I}{N} - (m_s + \delta) S_q, \\
A' &= \beta_s(1 - \rho_s)\varepsilon_s \frac{S I}{N} - (\gamma_a + \xi_a + \delta) A, \\
I' &= \gamma_a A - (\gamma_i + \xi_i + \delta) I, \\
I_q' &= \beta_s\varepsilon_s\rho_s \frac{S I}{N} + \gamma_i I - (\xi_q + \delta) I_q, \\
R' &= \xi_a A + \xi_i I + \xi_q I_q - \delta R ,
\end{aligned}$$

where $\gamma_a$ is the progression rate from $A$ to $I$, $\gamma_i$ the isolation rate of symptomatic cases, and $\xi_a, \xi_i, \xi_q$ recovery rates. Only $I$ generates new infections.

**Proposition.** Take $\Lambda_s = \delta = 0$, as in the source's calibration. At the infection-free state ($S/N = 1$, $S_q = A = I = I_q = 0$), with infected compartments $(A, I, I_q)$,

$$R_0 = \rho(F V^{-1}) = \frac{\beta_s(1 - \rho_s)\varepsilon_s\, \gamma_a}{(\gamma_a + \xi_a)(\gamma_i + \xi_i)} .$$

Traced infected contacts enter $I_q$ directly and do not contribute; perfect tracing ($\rho_s \to 1$) drives $R_0$ to $0$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

At the infection-free state

$$F = \begin{pmatrix} 0 & \beta_s(1-\rho_s)\varepsilon_s & 0 \\ 0 & 0 & 0 \\ 0 & \beta_s\rho_s\varepsilon_s & 0\end{pmatrix}, \qquad V = \begin{pmatrix} \gamma_a + \xi_a & 0 & 0 \\ -\gamma_a & \gamma_i + \xi_i & 0 \\ 0 & -\gamma_i & \xi_q\end{pmatrix}.$$

Since $(V^{-1})_{21} = \gamma_a/\big((\gamma_a + \xi_a)(\gamma_i + \xi_i)\big)$ and $(V^{-1})_{22} = 1/(\gamma_i + \xi_i)$, the matrix $F V^{-1}$ has first row $\big(\beta_s(1-\rho_s)\varepsilon_s (V^{-1})_{21},\ \beta_s(1-\rho_s)\varepsilon_s (V^{-1})_{22},\ 0\big)$, a zero second row and a zero third column. Its characteristic polynomial is therefore $\lambda^2\big(\lambda - \beta_s(1-\rho_s)\varepsilon_s (V^{-1})_{21}\big)$, giving the formula. Interpretation: an untraced infected contact becomes asymptomatic, progresses to symptoms with probability $\gamma_a/(\gamma_a + \xi_a)$, and then transmits at rate $\beta_s\varepsilon_s$ for a mean time $1/(\gamma_i + \xi_i)$; the factor $1 - \rho_s$ is the untraced fraction.

## Sources

- K. Sarkar, S. Khajanchi and J. J. Nieto, *Modeling and forecasting the COVID-19 pandemic in India*, Chaos, Solitons & Fractals (2020). <https://doi.org/10.1016/j.chaos.2020.110049> (PMCID: PMC7321056). Section 2, system (1), and Section 2.1, Equation (3).
