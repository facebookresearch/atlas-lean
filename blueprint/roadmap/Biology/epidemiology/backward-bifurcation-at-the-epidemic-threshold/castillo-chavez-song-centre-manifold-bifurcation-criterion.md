# Castillo-Chavez–Song centre-manifold bifurcation criterion

**Setting.** Consider $\dot x = f(x, \phi)$ with $x \in \mathbb{R}^n$, a bifurcation parameter $\phi \in \mathbb{R}$, and $f$ of class $C^2$ in $(x, \phi)$, with $f(0, \phi) = 0$ for all $\phi$ (after translating the disease-free equilibrium to $0$ and shifting the parameter so that $\phi = 0$ corresponds to $\mathcal{R}_0 = 1$). Assume:

- **(A1)** $A = D_x f(0, 0)$ has a simple zero eigenvalue and all other eigenvalues have negative real parts;
- **(A2)** $A$ has a right eigenvector $w$ and a left eigenvector $v$ for the zero eigenvalue, normalized by $v \cdot w = 1$.

Define

$$a = \sum_{k,i,j=1}^{n} v_k w_i w_j \frac{\partial^2 f_k}{\partial x_i \partial x_j}(0, 0), \qquad b = \sum_{k,i=1}^{n} v_k w_i \frac{\partial^2 f_k}{\partial x_i \partial \phi}(0, 0).$$

**Theorem.** The local dynamics near $x = 0$, $\phi = 0$ are determined by the signs of $a$ and $b$:

1. $a > 0$, $b > 0$: for $\phi < 0$ with $|\phi| \ll 1$, $0$ is locally asymptotically stable and there is a positive unstable equilibrium; for $0 < \phi \ll 1$, $0$ is unstable and there is a negative, locally asymptotically stable equilibrium.
2. $a < 0$, $b < 0$: for $\phi < 0$, $0$ is unstable; for $0 < \phi \ll 1$, $0$ is locally asymptotically stable and there is a positive unstable equilibrium.
3. $a > 0$, $b < 0$: for $\phi < 0$, $0$ is unstable and there is a locally asymptotically stable negative equilibrium; for $0 < \phi \ll 1$, $0$ is stable and a positive unstable equilibrium appears.
4. $a < 0$, $b > 0$: as $\phi$ passes from negative to positive, $0$ changes from stable to unstable, and a negative unstable equilibrium becomes positive and locally asymptotically stable.

**Epidemiological corollary.** With $\phi = \beta - \beta^*$, where $\beta^*$ is the transmission rate at which $\mathcal{R}_0 = 1$, and $b > 0$ (the usual case), the model undergoes a **backward bifurcation** at $\mathcal{R}_0 = 1$ when $a > 0$ (a positive unstable endemic branch exists for $\mathcal{R}_0 < 1$, coexisting with the stable disease-free equilibrium and a stable endemic equilibrium) and a **forward bifurcation** when $a < 0$ (a locally stable endemic equilibrium exists only for $\mathcal{R}_0 > 1$). The requirement that $w$ be nonnegative may be relaxed in the components corresponding to compartments that are positive at the disease-free equilibrium (for example susceptibles).

## Expansion

The proof restricts the flow to the one-dimensional centre manifold through $(0, 0)$ tangent to $w$. Writing $x = c\, w + O(c^2, c\phi)$, the reduced equation is $\dot c = \tfrac12 a c^2 + b \phi c + O(|c|^3 + \phi^2|c|)$, the normal form of a transcritical bifurcation, whose nontrivial equilibrium $c^* \approx -2 b \phi / a$ has sign $-\mathrm{sign}(ab\phi)$ and stability opposite to that of $c = 0$. In epidemic models $w$ and $v$ are computed from the Jacobian at the disease-free equilibrium at $\beta = \beta^*$; typically $v_k = 0$ for uninfected compartments, so only second derivatives of the infected equations enter $a$, and the sign of $a$ reflects whether reinfection-type nonlinearities (terms that increase infection when infected numbers rise) outweigh the depletion of susceptibles. Under a backward bifurcation, bringing $\mathcal{R}_0$ below one no longer guarantees elimination; the disease-free equilibrium is then not globally stable and the [Castillo-Chavez–Feng–Huang criterion](../global-stability-of-disease-free-equilibria/castillo-chavez-feng-huang-global-stability-criterion.md) must fail.

## Sources

- C. Castillo-Chavez, B. Song, "Dynamical models of tuberculosis and their applications", Mathematical Biosciences and Engineering 1 (2004) 361–404, Theorem 4.1, <https://doi.org/10.3934/mbe.2004.1.361>.
- S. M. Kassa, J. B. H. Njagarah, Y. A. Terefe, "Analysis of the mitigation strategies for COVID-19: From mathematical modelling perspective", Chaos, Solitons and Fractals 138 (2020) 109968, Theorem 3.3 and Appendix B (bifurcation coefficients (32)–(33)), <https://doi.org/10.1016/j.chaos.2020.109968>.
- S. W. Teklu, K. P. Rao, "HIV/AIDS-Pneumonia Codynamics Model Analysis with Vaccination and Treatment", Computational and Mathematical Methods in Medicine 2022 (2022) 3105734, Theorem 5 (backward bifurcation of the pneumonia submodel at $\mathcal{R}_2 = 1$), <https://doi.org/10.1155/2022/3105734>.
