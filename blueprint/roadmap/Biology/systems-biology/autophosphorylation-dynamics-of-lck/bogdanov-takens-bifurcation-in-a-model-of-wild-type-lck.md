# Bogdanov–Takens bifurcation in a model of wild-type Lck

Wild-type Lck has an activating tyrosine phosphorylated by autophosphorylation and an inhibitory tyrosine phosphorylated by an external kinase. Let $x_1, x_2$ be the concentrations of the two main forms of Lck (in the basic model of autophosphorylation, X and its inhibited form), $y$ the remaining Lck forms, $x_4$ the fast complex of the external kinase, and $X = x_1 + x_2 + y$ the conserved total. In the fast-binding limit $x_4 = y/(1+\xi)$ with $\xi = k_6/k_5$, and the dynamics reduce to the planar system

$$

\begin{aligned}
\dot x_1 &= -k_2x_1 + k_1x_2 + k_4\,\frac{\xi\,(X - x_1 - x_2)}{\beta(\xi+1) + \xi(X - x_1 - x_2)} - k_3x_1\big[(X - x_1 - x_2) + \delta x_1\big],\\
\dot x_2 &= k_2x_1 - k_1x_2 + \frac{k_7}{\xi + 1}\,(X - x_1 - x_2),
\end{aligned}

$$

with positive rate constants $k_i$ and parameters $\beta, \delta > 0$.

**Theorem.** There are parameter values for which this system undergoes a generic Bogdanov–Takens bifurcation. Consequently, for nearby parameters it has an unstable periodic solution, and for others a homoclinic orbit. When the unstable periodic solution exists close to the bifurcation point, the system also has two stable steady states and one saddle.

So the model of wild-type Lck combines bistability with oscillatory transients, in contrast to the single-site model without the inhibitory site, which has no periodic solutions.

## Expansion

A Bogdanov–Takens point is an equilibrium whose linearization has a double zero eigenvalue with a single Jordan block. One solves for parameters making both the trace and determinant of the Jacobian vanish at a positive equilibrium, then verifies the two nondegeneracy coefficients of the normal form and transversality in two unfolding parameters. The unfolding of a generic Bogdanov–Takens point contains a Hopf curve and a homoclinic curve, which yields the periodic and homoclinic orbits; the extra stable equilibria come from a nearby cusp-type fold structure of the steady-state set.

## Sources

- Lisa Maria Kreusser, Alan D. Rendall, "Autophosphorylation and the dynamics of the activation of Lck", arXiv (2021); Bulletin of Mathematical Biology (2021). Section 5 (reduced model and Theorem 5). <https://doi.org/10.48550/arXiv.2101.09295>. Published version: Bulletin of Mathematical Biology 83(6) (2021), article 64, <https://doi.org/10.1007/s11538-021-00900-9>; locators above refer to the arXiv version.
