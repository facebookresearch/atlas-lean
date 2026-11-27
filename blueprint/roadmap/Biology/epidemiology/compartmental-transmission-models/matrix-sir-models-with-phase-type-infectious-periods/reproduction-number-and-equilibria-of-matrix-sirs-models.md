# Reproduction number and equilibria of matrix SIRS (Arino-type) models with phase-type disease stages

**Model.** A matrix SIRS epidemic of type $(1, n, p)$ has one susceptible class $s$, a row vector $\vec i$ of $n$ disease stages (latent, infectious, asymptomatic, and so on), and a row vector $\vec r$ of $p$ removed states. In scaled (proportion) form with birth rate $\Lambda$,

$$
\begin{aligned}
s' &= \Lambda - (\Lambda + \gamma_s)s + \vec r\,\boldsymbol\gamma_r - s\,\vec i\,\mathbf b + \Phi_s\, s\,(\vec i\,\boldsymbol\nu + \vec r\,\boldsymbol\nu_r), \\
\vec i' &= \vec i\,\big(s B + A - \mathrm{Diag}(\boldsymbol\nu + \Lambda\mathbf 1)\big) + \Phi_i\, \vec i\,(\vec i\,\boldsymbol\nu + \vec r\,\boldsymbol\nu_r), \\
\vec r' &= s\,\vec\gamma_s + \vec i\,W - \vec r\,\mathrm{Diag}(\boldsymbol\gamma_r + \boldsymbol\nu_r + \Lambda\mathbf 1) + \Phi_r\, \vec r\,(\vec i\,\boldsymbol\nu + \vec r\,\boldsymbol\nu_r),
\end{aligned}
$$

with $s + \vec i\mathbf 1 + \vec r\mathbf 1 = 1$. Here $B$ is the infection matrix with $\mathbf b = B\mathbf 1$, $A$ is a Metzler matrix of stage transitions (a phase-type sub-generator), $W$ routes exits to removed states, $\boldsymbol\nu, \boldsymbol\nu_r$ are disease and vaccination fatality rates, $\vec\gamma_s$ is the vaccination rate vector with $\gamma_s = \vec\gamma_s\mathbf 1$, and $\boldsymbol\gamma_r$ is the vector of immunity-loss rates. Taking $\Phi_s = \Phi_i = \Phi_r = 1$ gives the exact scaled model; $\Phi \equiv 0$ is the first approximation, and $\Phi_s = \Phi_r = 1$, $\Phi_i = 0$ the intermediate approximation. The SIR-PH case has a single removed class and $W = \mathbf a = (-A)\mathbf 1$.

**Proposition (SIR-PH threshold).** Let $\Lambda = \mu$ and $V = \mathrm{Diag}(\boldsymbol\nu + \Lambda\mathbf 1) - A$.

1. If $\nu_r = 0$, the unique disease-free equilibrium is $\big(\tfrac{\Lambda + \gamma_r}{\Lambda + \gamma_r + \gamma_s}, \vec 0, \tfrac{\gamma_s}{\Lambda + \gamma_r + \gamma_s}\big)$. If $\nu_r > 0$ (excluding $\Lambda = \gamma_r = 0$), it is unique with $s_{dfe}$ the positive root of $\nu_r s^2 + (\Lambda + \gamma_r + \gamma_s - \nu_r)s - (\Lambda + \gamma_r) = 0$.
2. With $F = s_{dfe}B$, the threshold $\mathcal R = \lambda_{PF}(FV^{-1})$ satisfies the weak $\mathcal R$ alternative: the disease-free equilibrium is locally asymptotically stable if $\mathcal R < 1$ and unstable if $\mathcal R > 1$.
3. For rank-one infection $B = \mathbf b\,\vec\alpha$ and $\nu_r = 0$,

$$
\mathcal R = s_{dfe}\,\mathcal R_0, \qquad \mathcal R_0 = \vec\alpha\, V^{-1}\mathbf b,
$$

and if $\mathcal R \le 1$ and the nonlinear perturbation is nonnegative, $Y = \vec i\, V^{-1}\mathbf b$ is a Lyapunov function for the disease-free equilibrium.

**Proposition (endemic point).** Let $\mathcal R > 1$, assume $\boldsymbol\nu_r = 0$ or that $B$ has rank one, and consider either the first or the intermediate approximation ($\Phi_i = 0$), or the exact scaled model with no fatalities ($\boldsymbol\nu = \boldsymbol\nu_r = 0$). Then the system has a unique endemic fixed point in its invariant set. There $1/s_{ee}$ is an eigenvalue of $BV^{-1}$ (in the SIR-PH case, $1/s_{ee} = \mathcal R_0$), and $\vec i_{ee}$ is a Perron–Frobenius left null vector of $s_{ee}B + A - \mathrm{Diag}(\boldsymbol\nu + \Lambda\mathbf 1)$, normalized by an explicit linear equation. With $\boldsymbol\nu_r = 0$, the scaled model and both approximations share the same disease-free equilibrium.

For the exact scaled model with fatalities ($\Phi_i = 1$), the stage equation at an endemic point reads $\vec i\,(sB - V + c\,I_n) = 0$ with $c = \vec i\,\boldsymbol\nu + \vec r\,\boldsymbol\nu_r$, so $1/s_{ee}$ is an eigenvalue of $B(V - cI_n)^{-1}$ rather than of $BV^{-1}$, and in general $s_{ee} \ne 1/\mathcal R_0$: with one stage, $\Lambda = 1$, $A = -1$, $W = 1$, $B = 5$, $\nu = 1/2$ and $\gamma_s = \gamma_r = \nu_r = 0$, one has $\mathcal R_0 = 2$ but $s_{ee} \approx 0.4755$. The source's Proposition 3(c) does not name the model; its eigenvalue property holds only where $\Phi_i = 0$ or $c = 0$, which is the scope stated above.

## Depends on

- [Basic reproduction number from the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Starting from the disease-free state, a new infection enters stage $j$ with probability $\alpha_j$ and then moves through the stages according to the sub-generator $A$, killed at rates $\boldsymbol\nu + \Lambda$. The row vector $\vec\alpha V^{-1}$ is therefore the expected time spent in each stage, and $\vec\alpha V^{-1}\mathbf b$ is the expected number of infections caused. Rank-one $B$ makes $FV^{-1}$ rank one, so its Perron root is this scalar times $s_{dfe}$. Along trajectories, $Y' = \vec i\,\mathbf b\,(s\mathcal R_0 - 1) + (\text{nonlinear terms})$. Since $s \le s_{dfe}$ asymptotically, $Y$ is nonincreasing when $\mathcal R \le 1$. Phase-type stage structure contains the SIR, SEIR and Erlang $n$-stage models as special cases.

## Sources

- Florin Avram, Rim Adenane, Lasko Basnarkov, Gianluca Bianchin, Dan Goreac, Andrei Halanay, "On matrix-SIR Arino models with linear birth rate, loss of immunity, disease and vaccination fatalities, and their approximations", arXiv:2112.03436 (2021; no published version found). Definitions of the matrix SIR/V+S model and its scaled forms; Section 4 propositions on the basic reproduction number, the endemic point and the intermediate approximation. <https://doi.org/10.48550/arXiv.2112.03436>
