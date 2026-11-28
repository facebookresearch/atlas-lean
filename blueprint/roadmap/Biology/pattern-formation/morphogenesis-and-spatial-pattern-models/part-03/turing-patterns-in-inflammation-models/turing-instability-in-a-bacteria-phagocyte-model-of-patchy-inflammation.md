# Turing instability in a bacteria-phagocyte model of patchy intestinal inflammation

**Model.** On a long interval $\Omega \subset \mathbb{R}$ (a segment of the gut) with Neumann boundary conditions, let $\beta(t,x)$ be the density of bacteria that have crossed the epithelial barrier and $\gamma(t,x)$ the density of phagocytes:

$$
\begin{aligned}
\partial_t \beta - d_b\, \Delta \beta &= r_b\Big(1 - \frac{\beta}{b_i}\Big)\beta - \frac{a\, \beta\, \gamma}{s_b + \beta} + f_e\Big(1 - \frac{\beta}{b_i}\Big)\gamma,\\
\partial_t \gamma - d_c\, \Delta \gamma &= f_b\, \beta - r_c\, \gamma,
\end{aligned}
$$

with positive parameters: diffusivities $d_b, d_c$, bacterial growth rate $r_b$, luminal bacterial density $b_i$ (a carrying capacity), Holling type II phagocytosis with maximal rate $a$ and half-saturation $s_b$, epithelial damage caused by phagocytes $f_e$, recruitment rate $f_b$ and phagocyte death rate $r_c$.

**Invariant region.** Non-negative initial data give non-negative solutions; if $\beta_0 < b_i$ then $\beta(t, \cdot) < b_i$ for all $t > 0$, and $\gamma(t, \cdot)$ stays bounded in $L^2(\Omega)$.

**Equilibria.** Besides the unstable trivial state $(0,0)$, there is a unique positive homogeneous steady state $(\bar\beta, \bar\gamma)$ with $\bar\beta \in (0, b_i)$, $\bar\gamma = \kappa \bar\beta$, $\kappa = f_b / r_c$, and

$$
(r_b + f_e \kappa)\Big(1 - \frac{\bar\beta}{b_i}\Big) = \frac{a\, \kappa\, \bar\beta}{s_b + \bar\beta}.
$$

Write $\theta = \bar\beta / b_i$ and

$$
J_{11} = \frac{a\, \kappa\, \bar\beta^2}{(s_b + \bar\beta)^2} - r_b\, \theta - f_e\, \kappa ,
$$

which is the derivative of the bacterial reaction term with respect to $\beta$ at $(\bar\beta, \bar\gamma)$.

**Proposition (kinetic stability).** For the reaction system without diffusion, $(\bar\beta, \bar\gamma)$ is linearly stable if and only if $J_{11} < r_c$.

**Proposition (Turing instability).** If

$$
0 < J_{11} < r_c ,
$$

then for $\delta = d_b / d_c$ small enough the reaction-diffusion system has Turing instabilities around $(\bar\beta, \bar\gamma)$: the homogeneous state is stable for the kinetics but a bounded band of spatial modes grows exponentially. The parameter set satisfying the condition is non-empty and contains values consistent with measured bacterial doubling times and phagocyte half-lives.

## Expansion

At $(\bar\beta, \bar\gamma)$ the Jacobian is $\begin{pmatrix} J_{11} & J_{12} \\ f_b & -r_c\end{pmatrix}$ with $J_{12} = -a\bar\beta/(s_b + \bar\beta) + f_e(1 - \theta)$, and the equilibrium relation shows that the determinant $-r_c J_{11} - f_b J_{12}$ is positive. Kinetic stability therefore reduces to a negative trace, $J_{11} - r_c < 0$. For a Fourier mode $e^{ikx}$ the linearized matrix becomes $J - k^2 \operatorname{diag}(d_b, d_c)$, whose trace stays negative for all $k$. Its determinant

$$
h(k^2) = d_b d_c k^4 - (d_c J_{11} - d_b r_c)k^2 + \det J
$$

becomes negative for some $k^2 > 0$ exactly when $d_c J_{11} - d_b r_c > 2\sqrt{d_b d_c \det J}$. This requires $J_{11} > 0$ (bacteria act as a self-enhancing activator) and holds for small $\delta = d_b/d_c$ (phagocytes, the inhibitor, spread much faster). The unstable band is bounded, so the growing perturbation is spatially periodic, which the authors propose as a mechanism for the discontinuous, patchy inflamed segments characteristic of Crohn's disease.

## Depends on

- [Diffusion-driven instability (Turing 1952)](../../../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Proof depends on

- [Turing's criterion](../../../turing-patterns-and-diffusion-driven-instability/exists-is-unstable-mode-iff.md)

## Sources

- Grégoire Nadin, Eric Ogier-Denis, Ana Isis Toledo and Hatem Zaag, "A Turing mechanism in order to explain the patchy nature of Crohn's disease", arXiv (2020), Section 2 (model), Section 4 (propositions on non-negativity, boundedness, kinetic stability of the positive steady state and Turing instability), Section 5 (parameter estimates), <https://doi.org/10.48550/arXiv.2007.13587>.
- A. M. Turing, "The chemical basis of morphogenesis", Philosophical Transactions of the Royal Society B 237 (1952), 37–72, <https://doi.org/10.1098/rstb.1952.0012>.
