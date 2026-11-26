# Degenerate hyperbola separating antibody-only and CTL coexistence regimes

Consider healthy macrophages $M$, infected macrophages $I$, virus $V$, CTLs $C$ and antibodies $A$ with

$$\dot M = \lambda - \rho M - \beta MV,\quad \dot I = \beta MV - \delta I - kIC,\quad \dot V = bI - \gamma V - fVA,\quad \dot C = \psi IC - \omega C,\quad \dot A = \alpha V - \mu A,$$

all parameters positive (Hull-Nye et al. 2023, system (1)). The basic reproductive number is

$$R_0 = \frac{\beta\lambda b}{\delta\gamma\rho},$$

the infection-free equilibrium is globally asymptotically stable for $R_0 < 1$, and the second threshold is

$$R_1 = \frac{\hat V\beta\lambda\psi}{\delta\omega(\rho + \beta\hat V)}, \qquad \hat V = \frac{-\gamma\mu\psi + \sqrt{\gamma^2\mu^2\psi^2 + 4\psi f\alpha b\omega\mu}}{2\psi f\alpha},$$

with the antibody-only equilibrium stable for $R_1 < 1 < R_0$ and the coexistence equilibrium (antibodies and CTLs) stable for $1 < R_1 < R_0$ (Eqs. 2–4).

**Proposition.** In the $(\alpha, \psi)$ plane of antibody and CTL proliferation rates, the curve $R_1 = 1$ is the degenerate hyperbola

$$A\psi^2 + B\psi + C - D\alpha\psi = 0,$$

$$A = \beta\lambda\mu\omega\,\delta\gamma\rho\,(R_0 - 1) > 0,\quad B = \beta\mu\omega^2\delta\,\delta\gamma\rho\,(1 - 2R_0) < 0,\quad C = b\beta^2\delta^2\mu\omega^3 > 0,\quad D = \delta^2 f\omega^2\rho^2 > 0$$

(Lemma 1). It meets the $\psi$-axis at $\psi_1 = \delta\omega/\lambda$ and $\psi_2 = \frac{R_0}{R_0-1}\psi_1$; the coexistence region is the part above the upper branch (where also $\lambda\psi > \delta\omega$), and the boundary region lies below. The slant asymptote is $\psi = \frac{D}{A}\alpha - \frac{B}{A}$, with positive slope and positive intercept (Proposition 1). Hence stronger CTL proliferation or weaker antibody growth pushes the system toward coexistence.

## Expansion

On the boundary, $R_1 = 1$ means $\hat V = \delta\omega\rho/(\beta(\lambda\psi - \delta\omega))$, which requires $\psi > \psi_1$. At coexistence $I = \omega/\psi$ and $A = \alpha V/\mu$, so $\hat V$ solves $f\alpha V^2/\mu + \gamma V - b\omega/\psi = 0$, which is the displayed root. Substituting the first expression into this quadratic and clearing denominators gives the hyperbola with the stated coefficients; its discriminant form $\det\begin{pmatrix}0 & -D/2\\ -D/2 & A\end{pmatrix} = -D^2/4 < 0$ classifies it, and dividing by $D\psi$ shows $\alpha = (A/D)\psi + B/D + C/(D\psi)$, whose linear part gives the asymptote.

## Sources

- D. Hull-Nye, T. Meadows, S. R. Smith and E. J. Schwartz, *Key factors and parameter ranges for immune control of equine infectious anemia virus infection*, Viruses 15(3) (2023), 691, system (1), Eqs. (2)–(10), Lemma 1 and Proposition 1. <https://doi.org/10.3390/v15030691> (PMCID: PMC10058099)
