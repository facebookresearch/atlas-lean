# Explicit traveling bands for virus spread with logarithmic taxis

**Model.** A mobile viral density $\mathcal{V}(x,t)$ spreads through a stationary susceptible population $S(x,t)>0$ on the line by diffusion and by directed transport up the relative gradient of $S$, while depleting $S$ locally:

$$\mathcal{V}_t = D\mathcal{V}_{xx} - \partial_x\Big(\chi\,\mathcal{V}\,\frac{S_x}{S}\Big), \qquad S_t = -k\mathcal{V}, \qquad D,\chi,k>0.$$

**Theorem.** Let $d=\chi/D>1$, let $c>0$ be the wave speed, $s_+>0$ the susceptible density ahead of the wave, and $\alpha = c^2/(kD)$. Then for every $A>0$ there is a traveling band $\mathcal{V}=v(\zeta)$, $S=s(\zeta)$, $\zeta=x-ct$, defined on all of $\mathbb{R}^2$, with

$$s(\zeta) = s_+\big(1+Ae^{-c\zeta/D}\big)^{-1/(d-1)}, \qquad v(\zeta) = \frac{\alpha}{d-1}\,s(\zeta)\Big[1-\Big(\frac{s(\zeta)}{s_+}\Big)^{d-1}\Big].$$

The susceptible profile increases strictly from $0$ (behind the wave) to $s_+$ (ahead), and the viral profile is a single pulse that rises to a unique maximum and decays to zero at both ends. In terms of microscopic parameters with $D=\mu/(2\tau)$ and $\chi=\beta/\tau$, the condition reads $d = 2\beta/\mu\ge1$.

## Expansion

In the moving frame $S$-equation gives $c\,s' = k v$, so $v$ is proportional to $s'$; substituting into the viral equation and integrating once yields $Dv' - \chi v s'/s + cv = \text{const}$, which closes to a Bernoulli equation for $s$ whose solution is the explicit logistic-type profile. The relation $v = \frac{\alpha}{d-1}s - c_0s^{d}$ with $c_0 = \alpha/((d-1)s_+^{d-1})$ shows that the viral pulse vanishes exactly where $s\to0$ or $s\to s_+$, and the taxis strength $d>1$ is what allows a localised band rather than a front.

## Sources

- Y. Wang, A. Ibragimov, "On the spread of a virus and traveling waves, part I", arXiv:2610.04732, Section 2 (model) and Theorems 3.3–3.4. <https://doi.org/10.48550/arXiv.2610.04732>
