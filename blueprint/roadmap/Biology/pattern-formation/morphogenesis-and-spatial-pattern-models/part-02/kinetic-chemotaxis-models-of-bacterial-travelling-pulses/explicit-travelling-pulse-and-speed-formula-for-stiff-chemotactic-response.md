# Explicit travelling pulse and speed formula for a stiff chemotactic response

**Model.** Bacteria of density $\rho$ in a one-dimensional channel respond to a self-secreted chemoattractant $S$ and to a consumed nutrient $N$:

$$\partial_t\rho = D_\rho\partial_{xx}\rho - \partial_x\big(\rho u_S + \rho u_N\big),\qquad \partial_tS = D_S\partial_{xx}S - \alpha S + \beta\rho,\qquad \partial_tN = D_N\partial_{xx}N - \gamma\rho N .$$

In contrast with Keller–Segel, the chemotactic velocities are not proportional to gradients. They are derived from a run-and-tumble kinetic model, saturate at $\chi_S$ and $\chi_N$, and depend on the temporal change along a run. In the stiff-response limit,

$$u_S = \chi_S\Big(1 - \big(\epsilon\,\partial_tS/\partial_xS\big)^2\Big)_+\operatorname{sign}(\partial_xS),\qquad u_N = \chi_N\Big(1 - \big(\epsilon\,\partial_tN/\partial_xN\big)^2\Big)_+\operatorname{sign}(\partial_xN),$$

where $\epsilon$ is the ratio of pulse speed to individual cell speed.

**Result (travelling pulse).** Look for $\rho, S, N$ as functions of $z = x - \sigma t$ with $\sigma > 0$, $\rho, S\to0$ and $N\to N_\pm$ at $\pm\infty$, $N' > 0$, and $S$ maximal at $z=0$. Write $A = 1 - (\epsilon\sigma)^2$. Then the cell density is an asymmetric double exponential,

$$\rho(z) = \rho_0e^{\lambda^-z}\ (z<0),\qquad \rho(z) = \rho_0e^{\lambda^+z}\ (z>0),$$

$$\lambda^- = \frac{-\sigma + (\chi_S+\chi_N)A}{D_\rho} > 0,\qquad \lambda^+ = \frac{-\sigma + (\chi_N - \chi_S)A}{D_\rho} < 0 .$$

The speed is determined by the condition $S'(0) = 0$, which becomes

$$\chi_N - \frac{\sigma}{1 - (\epsilon\sigma)^2} = \chi_S\,\frac{\sigma}{\sqrt{4D_S\alpha + \sigma^2}},$$

and this equation has a unique root $\sigma\in(0,\epsilon^{-1})$. The pulse speed is independent of the total number of cells $M = \rho_0(1/\lambda^- + 1/|\lambda^+|)$ and of the cell diffusivity $D_\rho$.

**Clusters.** Without nutrient, the stationary profile is $\rho(x) = \rho_0e^{-\chi_S|x|/D_\rho}$. Its width $D_\rho/\chi_S$ does not depend on the number of trapped cells, consistent with experiments on *E. coli* aggregates.

## Expansion

Under the ansatz, $u_N = \chi_N A$ is constant and $u_S = -\chi_SA\operatorname{sign}(z)$ jumps at the peak. Integrating the cell equation once gives $D_\rho\rho' = \rho(u_S + u_N - \sigma)$, hence the two exponentials. The chemoattractant is $S = K*\beta\rho$ with kernel $K(z) = a_1e^{-a_2|z| - a_3z}$, where $a_3 = \sigma/(2D_S)$, $a_2 = \sqrt{a_3^2 + \alpha/D_S}$ and $a_1 = 1/(2a_2D_S)$. Imposing $S'(0) = 0$ gives $\lambda^-/|\lambda^+| = (a_2+a_3)/(a_2-a_3)$. Cross-multiplying and dividing by $A\sqrt{4D_S\alpha + \sigma^2}$ yields the speed equation. Its left side decreases from $\chi_N$ to $-\infty$ on $(0,\epsilon^{-1})$, while its right side increases from $0$. The nutrient term pushes the pulse forward, the self-attraction holds it together, and the saturation of the kinetic fluxes is what makes the speed independent of mass. For a smooth (non-stiff) response function, the source studies cluster formation through the linear stability of the homogeneous state.

## Sources

- N. Bournaveas, A. Buguin, V. Calvez and B. Perthame, "Mathematical description of bacterial traveling pulses", arXiv:0912.1792 (2009), Section 2 (stiff-response travelling pulses, speed formula and cluster profile) and Appendix A (kinetic derivation), <https://doi.org/10.48550/arXiv.0912.1792>.
