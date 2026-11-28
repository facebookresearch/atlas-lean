# Elimination of intermediate species in mass-action networks

**Setting.** A *reaction network* has species, complexes (non-negative integer combinations of species) and reactions $y \to y'$ between complexes, each with mass-action rate $\kappa_{y\to y'} c^{y}$, where $c^{y} = \prod_i c_i^{y_i}$. An *intermediate* is a species $Y$ that is produced in at least one reaction, consumed in at least one reaction, and appears only in the complex consisting of $Y$ alone. A *core model* is a network on core complexes $y$ with core species concentrations $c$; an *extension model* of it has complexes that are core complexes or intermediates $Y_1, \dots, Y_p$ (concentrations $u_1, \dots, u_p$), has reactions only between these, and returns the core model when every path $y \to Y_{i_1} \to \dots \to Y_{i_k} \to y'$ through intermediates is collapsed into one reaction $y \to y'$ (directions preserved).

**Theorem (conservation laws).** The conservation laws of the core model are in one-to-one correspondence with those of any extension model: each extension law is a core law plus a linear combination of the $u_i$. Consequently core and extension models have the same number of connected components of the reaction graph and the same deficiency.

**Theorem (elimination).** The equations $\dot u_i = 0$ for all intermediates can always be solved, and at steady state

$$u_i = \sum_{y} \mu_{i,y}\, c^{y},$$

where each $\mu_{i,y} \ge 0$ is a rational function of the extension rate constants only, and $\mu_{i,y} > 0$ if and only if there is a reaction path $y \to \dots \to Y_i$ passing only through intermediates.

**Theorem (reduced kinetics).** Substituting these expressions into the equations for $\dot c$ gives a mass-action system for the core model with rate constants

$$\tau_{y\to y'} = \kappa_{y\to y'} + \sum_{j=1}^p \kappa_{Y_j \to y'}\, \mu_{j,y},$$

so steady states of the extension model are in bijection with pairs (steady state $c$ of the core model with constants $\tau$, the induced $u$).

**Corollary (canonical models).** Group extension models by their *class complexes*, the core complexes that contain a species appearing in some conservation law and react directly to an intermediate. The canonical model of a class adds one dead-end reaction $y \rightleftharpoons Y$ for each class complex. If the canonical model of a class has at most $N$ positive steady states for all rate constants and conserved amounts, then every extension model in that class or in any smaller class (one whose class complexes are a subset of this class's), the core model included, has at most $N$ positive steady states. Conversely, if the core model has $N$ non-degenerate positive steady states in one stoichiometric class for constants $\tau$ that an extension model can realize, the extension model has at least $N$ non-degenerate positive steady states for suitable constants and conserved amounts.

## Proof sketch

The intermediate equations are linear in $u$: $\dot u = A u + z(c)$, with $z$ a vector of core monomials and $A$ a compartmental matrix whose eigenvalues all have negative real part, so $u = -A^{-1} z(c)$; the matrix-tree theorem gives the positivity pattern of $-A^{-1}$ in terms of directed paths among intermediates. Substituting into the core equations collapses each path to an effective reaction, which is the familiar quasi-steady-state reduction, here exact at steady state and requiring no time-scale separation. Conservation laws correspond because every intermediate lies in exactly one connected component, so each core law extends by assigning to $Y_i$ the value the law takes on the complexes of its component. Multistationarity lifts by the implicit function theorem when the $\mu$'s are made small; the upper bound uses that the canonical model has the largest realizable parameter set within its class.

## Sources

- Elisenda Feliu and Carsten Wiuf, "Simplifying biochemical models with intermediate species", *Journal of The Royal Society Interface* 10 (2013), 20130484, <https://doi.org/10.1098/rsif.2013.0484>. Preprint version: arXiv:1303.6737 (2013), Sections 2-5, Theorems 1-4 and Corollary 1, <https://doi.org/10.48550/arXiv.1303.6737>.
