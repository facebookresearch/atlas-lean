# Moving exponential releases of sterile males reverse a monostable mosquito front

**Model.** On $x\in\mathbb R$, let $E$ be the aquatic stage, $F$ adult females, $M$ fertile adult males and $M_s$ sterile males released at rate $\Lambda(t,x)$:

$$\partial_tE = \beta F\Big(1 - \frac EK\Big) - (\nu_E + \mu_E)E, \qquad \partial_tF - D\partial_{xx}F = r\nu_EE\,\frac{M}{M + \gamma M_s} - \mu_FF,$$

$$\partial_tM - D\partial_{xx}M = (1-r)\nu_EE - \mu_MM, \qquad \partial_tM_s - D\partial_{xx}M_s = \Lambda(t,x) - \mu_sM_s,$$

with birth rate $\beta$, carrying capacity $K$, emergence rate $\nu_E$, death rates $\mu_E,\mu_F,\mu_M,\mu_s$, female fraction $r\in(0,1)$, diffusion $D$, and competitiveness $\gamma$ of sterile males. The **basic offspring number** is

$$\mathcal R = \frac{\beta r\nu_E}{\mu_F(\nu_E + \mu_E)}.$$

If $\mathcal R > 1$ the uncontrolled system has the positive equilibrium $E^\ast = K\frac{\beta r\nu_E - \mu_F(\nu_E+\mu_E)}{\beta r\nu_E}$, $F^\ast = K\frac{\beta r\nu_E - \mu_F(\nu_E+\mu_E)}{\beta\mu_F}$, $M^\ast = K\frac{1-r}{r}\frac{\beta r\nu_E - \mu_F(\nu_E+\mu_E)}{\beta\mu_M}$.

**Theorem.**

1. (Natural invasion.) If $\mathcal R > 1$ and $\Lambda\equiv0$, there is a minimal speed $\bar c > 0$ such that for every $c\ge\bar c$ the system has a non-increasing traveling wave $(E,F,M)(x - ct)$ connecting $(E^\ast,F^\ast,M^\ast)$ at $-\infty$ to $(0,0,0)$ at $+\infty$.
2. (Comparison principle.) Although the system is not cooperative once $M_s > 0$, ordered release rates $0\le M_s^2\le M_s^1$ preserve order: a sub-solution with $M_s^1$ that starts below a super-solution with $M_s^2$ stays below it.
3. (Front reversal by a moving release.) If $\mathcal R > 1$, $0\le(E^0,F^0,M^0)\le(E^\ast,F^\ast,M^\ast)$ and the initial population vanishes on $\mathbb R_+$, then for every speed $c\le0$ there are $A,\eta > 0$ such that the release

$$\Lambda(t,x) = \begin{cases}0, & x - ct\le0,\\ Ae^{-\eta(x-ct)}, & x - ct > 0,\end{cases}$$

gives $\lim_{t\to\infty}\sup_{x > ct}\max(E,F,M)(t,x) = 0$. The total number released per unit time is the finite amount $A/\eta$, and the mosquito front is pushed towards $-\infty$ at speed $|c|$.

## Depends on

- [Fisher–KPP travelling waves](../../../pattern-formation/fisher-kpp-travelling-waves/README.md)

## Expansion

Without releases the system is monostable and cooperative on $\{E\le K\}$, so fronts exist for all speeds above a minimal one by the theory of monostable systems; this is the hair-trigger effect. The sterile males make the female recruitment term decreasing in $M_s$, which breaks cooperativity, but monotonicity in the control is enough for a comparison principle. In the moving frame $z = x - ct$, a scalar toy model with an Allee-type term created by the sterile-male fraction admits an exponential super-solution equal to the equilibrium for $z < 0$ and decaying like $e^{r z}$ for $z\ge0$; choosing $A$ large and $\eta$ small makes the release dense enough ahead of the front to dominate, and the comparison principle transfers the construction to the full system, forcing extinction on $\{x > ct\}$.

## Sources

- Alexis Léculier, Nga Nguyen, "A control strategy for Sterile Insect Techniques using exponentially decreasing releases to avoid the hair-trigger effect", arXiv (2022). Section 1.2 (model, $\mathcal R$, Theorem 1), Section 3 (simplified model, Theorems 3 and 5, Proposition 4; Theorem 7, Theorem 8, Proposition 9). <https://doi.org/10.48550/arXiv.2211.07701>. Published version: Mathematical Modelling of Natural Phenomena 18 (2023), article 25, <https://doi.org/10.1051/mmnp/2023018>; locators above refer to the arXiv version.
