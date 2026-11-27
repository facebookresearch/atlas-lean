# Monotone systems with positive feedback: the input–output characteristic test

Let $\dot x = f(x, \omega)$, $\eta = h(x)$ be a monotone input–output system with a single input and a single output (monotone with respect to an orthant order on states and the standard order of the real line on input and output, the setting of Angeli and Sontag 2004, Theorem 3) that has a well-defined input–output characteristic $k$: for each constant input $\omega$ there is a unique globally asymptotically stable equilibrium $\bar x(\omega)$, whose output is $k(\omega)$. Close the loop with unity positive feedback, $\omega = \eta$. Angeli, Ferrell and Sontag (2004) show that the equilibria of the closed loop correspond one-to-one to the fixed points of $k$. Assume in addition (Angeli and Sontag 2004, Definition 2.1 and Theorem 3) that the characteristic is nondegenerate, meaning that each constant-input equilibrium is nondegenerate: the Jacobian $\partial f/\partial x\,(\bar x(\omega), \omega)$ is nonsingular; that the closed-loop flow $\dot x = f(x, h(x))$ is strongly monotone; that all closed-loop trajectories are bounded; and that $k'(\omega) \ne 1$ at every fixed point of $k$. Then for all initial conditions outside a set of measure zero the closed-loop solutions converge to equilibria corresponding to fixed points with $k'(\omega) < 1$. The scalar condition $k'(\omega) \ne 1$ concerns the fixed points of $k$ and does not replace nondegeneracy of the open-loop equilibria. This turns bistability of positive-feedback loops into a test on a scalar curve.

## Expansion

1. The model: monotone control systems, input–output characteristics, nondegenerate characteristics, and the closed loop.
2. The correspondence between closed-loop equilibria and fixed points of $k$.
3. Stability of the equilibria according to $k' < 1$ or $k' > 1$.
4. Generic convergence: Hirsch's theorem for strongly monotone flows (convergence of almost every bounded solution to equilibria), applied to the closed-loop flow, which is assumed strongly monotone.
5. The biochemical applications (MAPK cascades, Cdc2–cyclin feedback), as separate statements.

## Sources

- D. Angeli, J. E. Ferrell Jr. and E. D. Sontag, Detection of multistability, bifurcations, and hysteresis in a large class of biological positive-feedback systems, Proc. Natl. Acad. Sci. USA 101 (2004), 1822–1827. <https://doi.org/10.1073/pnas.0308265100>
- D. Angeli and E. D. Sontag, Multi-stability in monotone input/output systems, Systems Control Lett. 51 (2004), 185–202. <https://doi.org/10.1016/j.sysconle.2003.08.003>
