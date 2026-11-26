# Timescale separation in the linear Michaelis–Menten system

**Setting.** The linear Michaelis–Menten system
$\dot x = k_1\begin{pmatrix} -e_0 & K_S\\ e_0 & -K_M\end{pmatrix} x$, $x = (s, c)$, with
$K_S = k_{-1}/k_1$, $K_M = (k_{-1}+k_2)/k_1$ and $K = k_2/k_1$, has eigenvalues

$$\lambda_{1,2} = \frac{k_1}{2}(K_M + e_0)\left(-1 \pm \sqrt{1 - \frac{4 K e_0}{(K_M + e_0)^2}}\right).$$

**Statement.** Linearity alone does not separate timescales: the two timescales
$|\lambda_1|^{-1}, |\lambda_2|^{-1}$ are comparable when $4 K e_0 \approx (K_M + e_0)^2$, for example
when $K_S \approx 0$ and $K_M \approx e_0$. A significant separation holds when

$$\frac{4 K e_0}{(K_M + e_0)^2} \ll 1,$$

which is the case, notably, when $e_0/K_M$ or $K/K_M$ is small. Under this condition:

1. the slow eigenvalue is $\lambda_1 \approx -\dfrac{k_2 e_0}{K_M + e_0}$, so the reduced equation is
   $\dfrac{d}{dt}(s, c)^{\mathsf T} = -\dfrac{k_2 e_0}{K_M + e_0}(s, c)^{\mathsf T}$;
2. the slow eigenspace is asymptotic to the span of
   $\hat v_1 = \left(K_M - \dfrac{K e_0}{K_M + e_0},\ e_0\right)^{\mathsf T}$.

This is a singular-perturbation reduction in the limit $\lambda_1 \to 0$.

## Depends on

- [Kamke comparison bounds for Michaelis–Menten kinetics at low substrate](kamke-comparison-bounds-for-michaelis-menten-at-low-substrate.md)

## Expansion

With $\Delta = k_1^2\big((K_M + e_0)^2 - 4 K e_0\big)$, the eigenvalues follow from trace
$-k_1(K_M + e_0)$ and determinant $k_1^2 e_0 K$. When $\varepsilon = 4Ke_0/(K_M+e_0)^2$ is small,
$\sqrt{1-\varepsilon} \approx 1 - \varepsilon/2$ gives $\lambda_1 \approx -k_1 K e_0/(K_M+e_0)$, and
the same Taylor step applied to the slow eigenvector $\big((K_M - e_0) + \sqrt{(K_M+e_0)^2 - 4Ke_0},\
2e_0\big)$ of the explicit linear solution yields $2\hat v_1$. The slow rate $k_2 e_0/(K_M + e_0)$
interpolates between the familiar pseudo-first-order rate $k_2 e_0/K_M$ (small $e_0$) and $k_2$
(enzyme in excess).

## Sources

- J. Eilertsen, S. Schnell, S. Walcher, "The Michaelis–Menten reaction at low substrate concentrations: pseudo-first-order kinetics and conditions for timescale separation", Bulletin of Mathematical Biology (2024), <https://doi.org/10.1007/s11538-024-01295-z> (PMC11069484). Section "Timescales for the linear Michaelis–Menten system", Eq. (9), Remark 5, Proposition 3 and its proof, Remark 6.
