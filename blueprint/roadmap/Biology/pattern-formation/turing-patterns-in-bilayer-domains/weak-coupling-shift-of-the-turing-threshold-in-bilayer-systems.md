# Weak-coupling shift of the Turing threshold in bilayer systems

**Model.** On an interval $(0,L)$, a surface layer with $n$ species $u_S$ and a thin bulk layer with $m \ge n$ species $u_B$ (the first $n$ of which, $\tilde u_B$, can cross the interface; $\tilde u_S$ denotes $u_S$ padded with zeros) evolve by

$$\partial_t u_S = f_S(u_S) + \eta A(\tilde u_B - u_S) + \partial_x\bigl(D_S(u_S)\partial_x u_S\bigr),$$

$$\partial_t u_B = f_B(u_B) + \eta \tilde B(\tilde u_S - u_B) + \partial_x\bigl(D_B(u_B)\partial_x u_B\bigr),$$

with coupling strength $\eta \ge 0$, nonnegative exchange matrices $A$, $\tilde B$, and diffusion matrices that may contain cross-diffusion (e.g. chemotaxis) terms. This 1D–1D system is the thin-bulk limit of a 1D surface over a 2D bulk with a linear flux condition at the interface. Let $w^*(\eta) = (u_S^*, u_B^*)$ be a homogeneous equilibrium, $J_S, J_B$ the reaction Jacobians, and for the squared wavenumber $\xi$ set $P_0 = \xi D_S - J_S$, $Q_0 = \xi D_B - J_B$ (evaluated at $\eta = 0$). Write $\operatorname{co}(M)$ for the cofactor matrix and $M \cdot N = \operatorname{Tr}(M^{\mathsf T}N)$.

Suppose the uncoupled surface layer undergoes a Turing bifurcation as a diffusion coefficient $\delta$ crosses $\delta_c(0)$ at squared wavenumber $\xi_c(0)$, i.e. $|P_0| = \partial_\xi|P_0| = 0$ while $|Q_0| \ne 0$ (surface-driven symmetry breaking), with the transversality condition $\partial^2_{\xi\xi}|P_0|\,\partial_\delta|P_0| \ne 0$. Then the critical value extends to a differentiable curve $\eta \mapsto \delta_c(\eta)$ near $0$, and:

1. **First-order shift.**

$$\delta_c'(0) = -\frac{\operatorname{co}(P_0)\cdot A + u_S^{*\prime}(0)\cdot\nabla_{u}|P_0|}{\partial_\delta|P_0|},$$

evaluated at $(\xi_c(0), \delta_c(0))$. To first order the shift does not depend on the bulk parameters except through the equilibrium drift $u_S^{*\prime}(0)$.
2. **Equilibrium drift.** If $J_S$ and $J_B$ are invertible, the equilibrium curve exists for small $\eta$ with $u_S^{*\prime}(0) = J_S^{-1}A\bigl(u_S^*(0) - \tilde u_B^*(0)\bigr)$. It vanishes when the two uncoupled layers share the same equilibrium, which is always the case for a surface over a 2D bulk.
3. **Shared equilibria.** If $u_S^*(0) = \tilde u_B^*(0)$ and $A = I$ (all surface species exchange equally), then $\delta_c'(0)$ and $\partial_\delta|P_0|$ have opposite signs: coupling always makes patterning harder. For pure reaction–diffusion surfaces ($D_S$ constant diagonal) some diagonal $A$ makes them have the same sign, so selective exchange can promote patterning.
4. **Activator–inhibitor case.** For two surface species with activator diffusion $1$, inhibitor diffusion $\delta = d_v$ satisfying the classical Turing conditions ($f_u > 0$, $g_v < 0$), shared equilibria and $A = \operatorname{diag}(\alpha, \beta)$,

$$\partial_\delta|P_0| < 0, \qquad \delta_c'(0) = \alpha\,\frac{\delta_c(0)}{\xi_c(0)}\Bigl(1 - \frac{\beta/\alpha}{\delta_c(0)}\Bigr),$$

so the coupling raises the inhibitor-diffusion threshold (inhibits patterning) iff $\beta < \alpha\,\delta_c(0)$, i.e. unless the inhibitor leaks through the interface fast enough relative to the activator.

## Depends on

- [Diffusion-driven instability (Turing 1952)](../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Expansion

Linearising about $w^*(\eta)$ in Fourier modes gives a block dispersion matrix whose determinant $a_0(\eta, w^*, \xi, \delta)$ at growth rate $0$ must satisfy $a_0 = \partial_\xi a_0 = 0$ at a Turing point. At $\eta = 0$ it factorises as $|P_0||Q_0|$, and Jacobi's formula $\frac{d}{dh}|M(h)| = \operatorname{co}(M)\cdot M'(h)$ gives $\partial_\eta a_0|_{\eta=0} = |Q_0|\operatorname{co}(P_0)\cdot A + |P_0|\operatorname{co}(Q_0)\cdot\tilde B$. Differentiating the two critical relations in $\eta$, the term with $|P_0| = 0$ drops and the implicit function theorem (enabled by transversality) yields item 1. Item 2 is the implicit function theorem applied to the equilibrium equations. With $A = I$, $\operatorname{co}(P_0)\cdot I$ is the sum of principal $(n-1)$-minors of $P_0$, which equals the product of its nonzero eigenvalues; at criticality these have positive real part, giving a positive numerator and item 3. In item 4, $\operatorname{co}(P_0)\cdot A = \alpha(\xi\delta - g_v) + \beta(\xi - f_u)$ and $\partial_\delta|P_0| = \xi(\xi - f_u)$, which combined with the classical relation $\xi_c = (\delta_c f_u + g_v)/(2\delta_c)$ gives the formula. Unequal layer equilibria add the drift term, which can either promote or suppress patterning depending on the direction of the concentration mismatch.

## Sources

- A. Diez, A. L. Krause, P. K. Maini, E. A. Gaffney, S. Seirin-Lee, "Turing pattern formation in reaction-cross-diffusion systems with a bilayer geometry", *Bulletin of Mathematical Biology* (2024), Sections 2–4 (Eqs. (10)–(14), (20)–(33), (37), Assumptions 1–2, Propositions 1–3 and 5), <https://doi.org/10.1007/s11538-023-01237-1> (PMC10764571).
