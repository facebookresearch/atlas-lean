# Competition thresholds in the additional-food predator–pest model

**Model.** Suppose the additional food (quantity $\xi$, quality $\alpha$) also induces intraspecific competition among predators, at a rate proportional to $\xi$:

$$\frac{dx}{dt}=x\Big(1-\frac x\gamma\Big)-\frac{xy}{1+\alpha\xi+x},\qquad \frac{dy}{dt}=\frac{\beta(x+\xi)y}{1+\alpha\xi+x}-\delta y-c\,\xi\,y^2,$$

with pest carrying capacity $\gamma$, conversion efficiency $\beta$, predator mortality $\delta$ and competition coefficient $c>0$. The pest-free state is $(0,y^*)$ with $y^*=\big((\beta-\delta\alpha)\xi-\delta\big)/\big(c\xi(1+\alpha\xi)\big)$.

**Theorem.** Assume $\dfrac{\delta}{\beta-\delta\alpha}<\xi<\dfrac1{1-\alpha}$ and define

$$c_2^*=\frac{4\gamma(\beta-\delta)}{\xi(1+\alpha\xi+\gamma)^2},\qquad c_3^*=\frac{(\beta-\delta\alpha)\xi-\delta}{\xi(1+\alpha\xi)^2}.$$

1. If $c>c_3^*$, the pest-free state $(0,y^*)$ is a saddle and there are one or three interior equilibria; if $c>\dfrac1{2\xi(1+\alpha\xi)}$ there is exactly one interior equilibrium and it is globally attracting (pest and predator coexist).
2. If $c_2^*<c<c_3^*$, then $(0,y^*)$ is locally stable and there are two interior equilibria, so bistability between pest eradication and coexistence is possible.
3. If $c<c_1^*=\min\Big(c_2^*,\ c_3^*,\ \dfrac{4\beta}{\xi}\,\dfrac{1+\alpha\xi-\xi}{1+\alpha\xi+\gamma}\,\dfrac{\gamma}{\gamma-(1+\alpha\xi)}\Big)$, then $(0,y^*)$ is globally stable and no interior equilibrium exists: the pest is eradicated with a bounded predator population.

For $\xi>1/(1-\alpha)$, increasing $c$ through $c_3^*$ is a transcritical bifurcation of the pest-free state, and a pitchfork bifurcation and a codimension-two pitchfork–transcritical organizing center occur in the $(c,\xi)$ plane.

## Depends on

- [Infinite-time predator blow-up under abundant additional food](infinite-time-predator-blow-up-under-abundant-additional-food.md)

## Expansion

The quadratic loss $c\xi y^2$ caps predator density at $y^*$, removing the blow-up. Linearizing at $(0,y^*)$, the pest's invasion rate is $1-y^*/(1+\alpha\xi)$, which is negative exactly when $c<c_3^*$; so weak competition keeps the predator dense enough to exclude the pest, while strong competition lets the pest invade. Interior equilibria are roots of a cubic obtained by intersecting the hump-shaped pest nullcline with the predator nullcline, which is concave down for $\xi<1/(1-\alpha)$; the discriminant governs whether one, two or three intersections exist. Biocontrol therefore succeeds with bounded predators only for an intermediate window of additional food and sufficiently weak food-induced competition.

## Sources

- Rana D. Parshad, Sureni Wickramsooriya, Kwadwo Antwi-Fordjour and Aniket Banerjee, "Additional Food Causes Predators to Explode — Unless the Predators Compete", International Journal of Bifurcation and Chaos 33 (2023), 2350034, <https://doi.org/10.1142/s0218127423500347>; numbering as in arXiv:2208.00153: Section 3 (model with competition), Theorem 4.4, Theorems 5.5, 5.6 and 5.7, and Section 6 (Theorems on transcritical, pitchfork and organizing-center bifurcations).
