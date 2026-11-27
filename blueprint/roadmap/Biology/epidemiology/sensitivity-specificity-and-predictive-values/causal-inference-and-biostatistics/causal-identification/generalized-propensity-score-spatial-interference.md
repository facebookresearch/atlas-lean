# Generalized propensity score as a balancing score under spatial interference

**Setting.** Units are locations $s$ in a domain $\mathcal D$ with a real exposure field $A_{\mathcal D} = (A_s)$, covariates $X_{\mathcal D}$ and outcomes $Y_s$. The spill-over exposure at $s$ is the kernel-weighted exposure of other locations,

$$\tilde A_{\tau, s} = \sum_{s' \ne s} \omega_\tau(\lVert s - s'\rVert)\, A_{s'} \quad\text{(or an integral over } \mathcal D \setminus \{s\}\text{)}, \qquad \omega_\tau : \mathbb R_+ \to [0, 1],$$

e.g. $\omega_\tau(d) = \exp(-(d/\tau)^2)$, and potential outcomes depend on the field only through $(a_s, \tilde a_{\tau, s})$: $Y_s(a_{\mathcal D}) = Y_s(a_s, \tilde a_{\tau,s})$. Assume (1) unconfoundedness $Y_s(a_s, \tilde a_{\tau, s}) \perp A_{\mathcal D} \mid X_{\mathcal D}$; (2) positivity of the exposure law given $X_{\mathcal D}$; (3) consistency $Y_s = Y_s(a_s, \tilde a_{\tau,s})$ when $A_s = a_s$, $\tilde A_{\tau,s} = \tilde a_{\tau,s}$; (4) the outcome model $Y_s(a_s, \tilde a_{\tau,s}) = \beta_0 + \delta_1 a_s + \delta_2 \tilde a_{\tau,s} + h(X_{\mathcal D})_s + \epsilon_s$ with $\epsilon_s$ independent of $(A_{\mathcal D}, X_{\mathcal D})$, where $\delta_1$ and $\delta_2$ are the direct and spill-over effects.

The **generalized propensity score** is the whole joint conditional density **function** of the two exposures,

$$g_{\tau, s}(X_{\mathcal D}) = \Bigl[(\eta, v) \mapsto f\bigl(A_s = \eta,\ \tilde A_{\tau, s} = v \mid X_{\mathcal D}\bigr)\Bigr], \qquad (\eta, v) \in \mathbb R^2,$$

a random element of a space of densities on $\mathbb R^2$, not its value at the observed exposures: two different exposure laws can share the same density value at the observed point. Equivalently one may condition on finite-dimensional parameters that determine this function: (5) the conditional law of $(A_s, \tilde A_{\tau, s})$ given $X_{\mathcal D}$ belongs to a known family $\{f_\vartheta\}$ indexed injectively by $\vartheta \in \mathbb R^r$, with $\vartheta = \vartheta_{\tau, s}(X_{\mathcal D})$ (for example a bivariate normal law with mean and covariance depending on $X_{\mathcal D}$), and the score is then $\vartheta_{\tau, s}(X_{\mathcal D})$.

**Theorem.** Under assumptions 1–4, for every location $s$ and exposure levels (and with the score replaced by $\vartheta_{\tau, s}(X_{\mathcal D})$ under assumption 5),

$$Y_s(a_s, \tilde a_{\tau, s}) \perp (A_s, \tilde A_{\tau, s}) \mid g_{\tau, s}(X_{\mathcal D}),$$

so $E[Y_s(a_s, \tilde a_{\tau,s}) \mid g_{\tau,s}] = E[Y_s \mid g_{\tau,s}, A_s = a_s, \tilde A_{\tau,s} = \tilde a_{\tau,s}]$ and $(\delta_1, \delta_2)$ are identified by regressing $Y_s$ on $(A_s, \tilde A_{\tau, s})$ and a function of $g_{\tau, s}$.

## Expansion

The conditional law of $(A_s, \tilde A_{\tau,s})$ given $X_{\mathcal D}$ is determined by the density function $g_{\tau, s}(X_{\mathcal D})$, which is itself a function of $X_{\mathcal D}$; hence the conditional law given $g_{\tau, s}(X_{\mathcal D})$ is the same density, and $(A_s, \tilde A_{\tau,s}) \perp X_{\mathcal D} \mid g_{\tau, s}(X_{\mathcal D})$, so conditioning on $g$ balances the exposures. A scalar ordinate such as the density value at the observed exposure does not determine the law and does not give this balance; combined with unconfoundedness given $X_{\mathcal D}$, iterated expectation shows that the exposure density given $(g, Y_s(\cdot))$ equals that given $g$. The dimension reduction matters because $X_{\mathcal D}$ is a whole spatial field.

## Sources

- A. Giffin, B. J. Reich, S. Yang et al., "Generalized propensity score approach to causal inference with spatial interference", *Biometrics* (2022), <https://doi.org/10.1111/biom.13745> (PMC10790180). Assumptions 1–4, equations (1)–(3), Theorem 1 and Corollary 1.
