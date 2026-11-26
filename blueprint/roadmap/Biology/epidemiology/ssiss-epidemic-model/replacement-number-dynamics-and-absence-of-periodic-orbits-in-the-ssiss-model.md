# Replacement-number dynamics and absence of periodic orbits in the SSISS model

**Model.** A population is split into two susceptible compartments $S_1, S_2$ (e.g. naive and recovered/vaccinated, with possibly reduced susceptibility) and an infectious compartment $I$, written as fractions with $S_1 + S_2 + I = 1$. With transfer rates $\alpha_1$ ($S_1 \to S_2$) and $\alpha_2$ ($S_2 \to S_1$), behaviour-induced transfers $\theta_i I$, incidence rates $\beta_i$, recovery rates $\gamma_i$ ($I \to S_i$), and constant per-capita birth rates $\delta_\bullet$ and death rates $\mu_\bullet$ (newborns entering $S_1$ or $S_2$ in proportions $q_1, q_2$), the fractional dynamics is
$$\dot{\mathbf S} = -\big[E(\tilde{\boldsymbol\alpha}) + I\,E(\boldsymbol\theta) + I\,D(\tilde{\boldsymbol\beta})\big]\mathbf S + I\tilde{\boldsymbol\gamma} + S_1S_2\begin{pmatrix}\nu_1-\nu_2\\ \nu_2-\nu_1\end{pmatrix},\qquad \dot I = \tilde\gamma\,(R_{\mathrm{eff}} - 1)\,I,$$
where $\mathbf S = (S_1,S_2)^\top$, $D(\boldsymbol\beta) = \operatorname{diag}(\beta_1,\beta_2)$, $E(\boldsymbol\alpha) = \begin{pmatrix}\alpha_1 & -\alpha_2\\ -\alpha_1 & \alpha_2\end{pmatrix}$, $\nu_\bullet = \delta_\bullet - \mu_\bullet$ is the net growth rate of each compartment, $\tilde\alpha_i, \tilde\gamma_i$ absorb the birth flows, $\tilde\beta_i = \beta_i + \nu_I - \nu_i$, $\tilde\gamma = \tilde\gamma_1 + \tilde\gamma_2$, and
$$R_{\mathrm{eff}} = \frac{\tilde\beta_1 S_1 + \tilde\beta_2 S_2}{\tilde\gamma}$$
is the replacement (effective reproduction) number.

**Proposition (redundancy of vital dynamics).** If $\nu_1 = \nu_2$, the fractional system has exactly the form of the constant-population model, so all birth and death parameters can be absorbed into $\tilde\alpha_i, \tilde\beta_i, \tilde\gamma_i$; the only price is that $\tilde\beta_i = \beta_i - \Delta\nu_I$, with $\Delta\nu_I = \nu_1 - \nu_I$ (the excess mortality of infectives under equal birth rates), may become negative. In particular, if $\Delta\nu_I \le \min\{\beta_1,\beta_2\}$ the variable-population model maps to a constant-population one.

**Theorem (no periodic orbits).** The SSISS system has no periodic solutions, homoclinic loops or oriented phase polygons in its phase triangle if either (i) all of $\tilde\alpha_i, \tilde\gamma_i, \theta_i$ are nonnegative, or (ii) the parameters lie in the biologically admissible region and $\nu_1 = \nu_2$. Hence every bounded orbit converges to an equilibrium.

**Symmetry.** There is a group $G_S \subset GL_+(\mathbb{R}^2)$ acting linearly on $(S_1,S_2)$ and on parameter space such that $G_S$-equivalent parameter sets give isomorphic dynamics; in the coordinates $(R_{\mathrm{eff}}, I)$ the model reduces to a normalized system with 5 essential parameters.

## Expansion

Multiplying the fractional equations by $N$ and using $\dot N/N = \nu_1S_1 + \nu_2S_2 + \nu_II$ produces the extra quadratic terms; when $\nu_1 = \nu_2$ the $S_1S_2$ term cancels and the remaining corrections are linear, hence absorbable into rescaled rates. Since $\dot I/I = \tilde\gamma(R_{\mathrm{eff}}-1)$, the replacement number together with $I$ forms natural coordinates, and the $G_S$ action changes $(\boldsymbol\beta, \mathbf S)$ while fixing $R_{\mathrm{eff}}$ and $I$. Periodic orbits are excluded with a Dulac function on the planar reduction to $(S_1, I)$ or $(R_{\mathrm{eff}}, I)$: with $1/I$-type weights the divergence has a fixed sign under the stated sign conditions.

## Sources

- Florian Nill, "Symmetries and normalization in 3-compartment epidemic models I: The replacement number dynamics", arXiv:2301.00159 (2022), Section 2 equations for constant and time-varying population and the proposition on variable population, Theorem 3.3, Proposition 4.1 and Corollaries 4.3 and 4.6, <https://doi.org/10.48550/arXiv.2301.00159>.
