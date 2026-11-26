# Basic viral dynamics model and its within-host basic reproductive number

The basic viral dynamics model describes a within-host infection by uninfected target cells $T(t)$, productively infected cells $I(t)$ and free virus $V(t)$, all nonnegative:

$$\dot T = \lambda - \beta T V - d_T T, \qquad \dot I = \beta T V - d_I I, \qquad \dot V = k I - c V,$$

with constant target-cell supply $\lambda > 0$, target-cell death rate $d_T > 0$, infectivity $\beta > 0$, infected-cell death rate $d_I > 0$ (typically $d_I > d_T$), virion production rate per infected cell $k > 0$ and virion clearance rate $c > 0$. Define the within-host basic reproductive number

$$R_0 = \frac{\lambda \beta k}{d_T\, d_I\, c}.$$

Then:

1. The infection-free equilibrium is $(T, I, V) = (\lambda/d_T, 0, 0)$.
2. An equilibrium with $I > 0$ exists if and only if $R_0 > 1$; it is

$$T^* = \frac{d_I c}{\beta k} = \frac{\lambda}{d_T R_0}, \qquad I^* = \frac{\lambda}{d_I}\Big(1 - \frac{1}{R_0}\Big), \qquad V^* = \frac{k}{c} I^*.$$

3. $R_0 = 1$ is a transcritical bifurcation: the infection-free equilibrium is locally asymptotically stable for $R_0 < 1$ and unstable for $R_0 > 1$, where the infected equilibrium takes over.
4. If a treatment blocks a fraction $\varepsilon \in [0, 1]$ of new infections, $\beta \mapsto (1-\varepsilon)\beta$, the treated reproductive number is $(1-\varepsilon) R_0$, and the infection is driven toward clearance exactly when

$$\varepsilon > 1 - \frac{1}{R_0}.$$

## Proof depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [Threshold theorem, stability half, conditional decay form](../../next-generation-matrix-and-the-basic-reproductio/global-solution-decay-of-r0-lt-one.md)
- [Threshold theorem, instability half, spectral form](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-jacobian-of-one-lt-r0.md)
- [Lyapunov's indirect method, instability](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)

## Proof sketch

$R_0$ is the expected number of cells infected by the virions released from one infected cell over its lifetime, $1/d_I$, in a target-cell population at its infection-free level $\lambda/d_T$: each infected cell releases $k/d_I$ virions, and each virion infects $\beta(\lambda/d_T)/c$ cells before clearance. Equivalently, with infected compartments $(I, V)$, transmission $F = \begin{pmatrix} 0 & \beta\lambda/d_T \\ 0 & 0 \end{pmatrix}$ and transitions $V = \begin{pmatrix} d_I & 0 \\ -k & c \end{pmatrix}$, the spectral radius of $F V^{-1}$ is $\lambda\beta k/(d_T d_I c)$. Setting $\dot I = \dot V = 0$ with $I \ne 0$ forces $\beta T k/c = d_I$, which gives $T^*$, and $\dot T = 0$ then gives $I^* = (\lambda - d_T T^*)/d_I$, positive iff $R_0 > 1$. The decline from peak viremia to a setpoint follows from target-cell limitation alone, because uninfected cells turn over more slowly than infected ones. Estimates of $R_0$ for HIV range from about 2 to 25, so suppression requires drug efficacy well above 90%. When several strains with different $\beta_i$ compete for the same target cells, the model shows competitive exclusion: the strain with the largest $R_0$ wins, the basis of the mutant selection window.

## Sources

- A. L. Hill, D. I. S. Rosenbloom, M. A. Nowak and R. F. Siliciano, "Insight into treatment of HIV infection from viral dynamics models", Immunological Reviews 285 (2018), Section 1.1 (Equations 1–2, Figure 2) and Section 2.3 (Equation 5), <https://doi.org/10.1111/imr.12698>, PMCID: PMC6155466.
