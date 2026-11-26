# Threshold dynamics of the SIRV model with logit vaccination decisions

**Model.** Susceptible, infected, recovered and vaccinated numbers satisfy

$$\dot S = A - \frac{\beta S I}{N^q} - dS - S\varphi, \quad \dot I = \frac{\beta S I}{N^q} - (r+d) I, \quad \dot R = rI - dR, \quad \dot V = S\varphi - dV,$$

with $N = S+I+R+V$, recruitment $A > 0$, death rate $d > 0$, recovery rate $r$, and incidence exponent $q \in [0,1]$ ($q=0$ bilinear, $q=1$ standard incidence). Since $\dot N = A - dN$, the region $\Gamma = \{(S,I,R,V) \in \mathbb{R}^4_+ : N \le A/d\}$ is positively invariant and globally attracting. Immunity from recovery and vaccination is permanent.

**Smoothed best-response vaccination.** A susceptible facing the decision weighs the benefit $W_p = \beta I/N^q$ (the force of infection avoided) against a constant perceived cost $W_n = \alpha > 0$ and vaccinates with probability

$$s(W) = \frac{e^{kW_p}}{e^{kW_p} + e^{kW_n}} = \frac{1 + \tanh(kW/2)}{2}, \qquad W = W_p - W_n,$$

where $k \ge 0$ is the degree of rationality. The per-capita vaccination rate is $\varphi = \phi\, s(W)$ with $\phi \in (0,1)$ the fraction of susceptibles facing the decision per unit time. As $k \to \infty$, $s$ tends to the best response ($1$ if $W>0$, $0$ if $W<0$, any value in $[0,1]$ if $W=0$); $k = 0$ gives $s \equiv 1/2$.

**Disease-free equilibrium and $\mathcal{R}_0$.** At $I = 0$, $s = (1-\tanh(k\alpha/2))/2$, so the disease-free equilibrium is $E_0 = (S_0^*, 0, 0, V_0^*)$ with

$$S_0^* = \frac{2A}{2d + \phi\,(1-\tanh(k\alpha/2))}, \qquad V_0^* = \frac{\phi A\,(1-\tanh(k\alpha/2))}{d\,\bigl(2d + \phi\,(1-\tanh(k\alpha/2))\bigr)},$$

and the next-generation method gives

$$\mathcal{R}_0 = \frac{2\beta A}{(A/d)^q\,(r+d)\,\bigl(2d + \phi\,(1-\tanh(k\alpha/2))\bigr)} .$$

**Theorem 1.** If $\mathcal{R}_0 < 1$, $E_0$ is the only equilibrium in $\Gamma$ and it is locally asymptotically stable; if $\mathcal{R}_0 > 1$, $E_0$ is unstable.

**Theorem 2.** If $\mathcal{R}_0 > 1$, an endemic equilibrium $E_1 = (S_1^*, I_1^*, R_1^*, V_1^*)$ exists in $\Gamma$ and is locally asymptotically stable.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

$\mathcal{R}_0$ is the basic reproduction number of an SIR model whose susceptible pool at the disease-free state is depleted by vaccination at rate $\phi\,s(-\alpha)$. Because $\tanh(k\alpha/2)$ increases with $k$ for $\alpha > 0$, $\mathcal{R}_0$ is increasing in $k$: the more precisely susceptibles respond to the payoff difference, the less they vaccinate when infection is rare and the harder it is to block initial spread. In the limit $k \to \infty$, $\mathcal{R}_0 \to \beta A/((A/d)^q (r+d)\, d)$, the value without vaccination, so a pure best-response population cannot eliminate the disease once its force of infection falls below the cost; the smoothed response keeps vaccinating at a positive rate and can. When $\alpha = 0$, $\mathcal{R}_0 = \beta A/((A/d)^q (r+d)(d + \phi/2))$, which exceeds the best-response value with denominator $d + \phi$, so with a costless vaccine the smoothed response is the less effective one. Existence of $E_1$ follows by reducing the equilibrium equations to the intersection of a decreasing and an increasing function of an auxiliary variable; stability follows from the Routh–Hurwitz conditions on the Jacobian.

## Sources

- F. Xu, R. Cressman, "Disease control through voluntary vaccination decisions based on the smoothed best response", Computational and Mathematical Methods in Medicine 2014 (2014) 825734, Equations (1)–(8), (23)–(24), Theorems 1 and 2, <https://doi.org/10.1155/2014/825734>, PMCID PMC3947699.
