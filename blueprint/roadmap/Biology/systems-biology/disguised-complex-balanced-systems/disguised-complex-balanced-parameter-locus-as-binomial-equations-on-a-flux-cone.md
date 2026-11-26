# Disguised complex-balanced parameter locus as binomial equations on a flux cone

**Setting.** A reaction network $(G, y)$ has a directed graph $G = (V, E)$ whose vertices are complexes $y(v) \in \mathbb{R}^n$; $V_s$ is the set of source vertices, $Y_s$ the matrix of source complexes and $I_{E,s}$ the source incidence matrix. Under mass action with rate constants $k \in \mathbb{R}^E_{>0}$ the reaction-rate vector is $v_k(x) = k \circ x^{Y_s I_{E,s}}$, and the system is $\dot x = \Gamma_k\, x^{Y_s}$, with $\Gamma_k$ collecting for each source vertex the rate-weighted sum of its reaction vectors $y(\text{target}) - y(\text{source})$. Two mass-action systems are *dynamically equal* if they define the same vector field. A system is *complex-balanced* at $x$ if the flux into each vertex equals the flux out; such systems have a unique, asymptotically and linearly stable positive equilibrium in each stoichiometric class. A system is *disguised complex-balanced* if it is dynamically equal to some complex-balanced system; $\mathcal{K}^{dCB}_{(G,y)} \subseteq \mathbb{R}^E_{>0}$ is the set of such rate constants.

**Reduction.** A complex-balanced realization can always be taken on the source vertices: there is a dynamically equal complex-balanced system iff there is one on the complete graph $G^{com}_{V_s}$ with vertex set contained in $V_s$ and the same complexes.

**Flux cone.** Let
$$\mathcal{C}^{dCB}_{(G,y)} = \big\{\nu \in \mathbb{R}^E_{\ge 0} : \exists\,\bar\nu \in \mathbb{R}^{E^{com}}_{\ge 0} \text{ with } I_{E^{com}}\bar\nu = 0 \text{ and } \Gamma_\nu = \Gamma_{\bar\nu}\big\},$$
the polyhedral cone of flux vectors on $G$ that produce the same source-wise net reaction vectors as some vertex-balanced flux $\bar\nu$ on the complete graph.

**Theorem.**
1. $\mathcal{K}^{dCB}_{(G,y)} = \{k \in \mathbb{R}^E_{>0} : \exists\, x \in \mathbb{R}^n_{>0},\ v_k(x) \in \mathcal{C}^{dCB}_{(G,y)}\}$, and the same holds with the cone replaced by its positive part.
2. (Elimination of concentrations.) With $\mathcal{P} = (\mathcal{C}^{dCB}_{(G,y)})_{>0} \cap \Delta$ (the positive part of the cone intersected with the simplex) and the monomial dependency subspace $\mathcal{D} = \ker\begin{pmatrix} Y_sI_{E,s} \\ \mathbf{1}^\top \end{pmatrix}$,
$$\mathcal{K}^{dCB}_{(G,y)} = \{k \in \mathbb{R}^E_{>0} : \exists\, \nu \in \mathcal{P} \text{ such that } \nu^z = k^z \text{ for all } z \in \mathcal{D}\}.$$
So the locus is the image of a polytope under finitely many binomial equations, with no concentration variables left.

## Depends on

- [Nondegenerate reaction networks have generically finite, nonsingular steady states](../generic-geometry-of-steady-state-varieties/nondegenerate-reaction-networks-have-generically-finite-nonsingular-steady-states.md)

## Expansion

Being disguised complex-balanced at $x$ is a linear condition on the rate vector $v_k(x)$: it must lie in the flux cone. So the locus is $\{k : \exists x,\ k \circ x^{B} \in \mathcal{C}\}$ with $B = Y_sI_{E,s}$, a parametrized system of generalized polynomial inequalities. The Müller–Regensburger theory of such systems writes the solution set as $\{(\nu \circ k^{-1})^{E'} : \nu \in \mathcal{Y}_k\}\circ e^{L^\perp}$, where $\mathcal{Y}_k = \{\nu \in P : \nu^z = k^z,\ z \in D\}$ lives on the coefficient polytope; nonemptiness of the $x$-solution set is equivalent to nonemptiness of $\mathcal{Y}_k$, which is exactly the binomial description.

## Sources

- S. Müller, A. Deshpande and G. Regensburger, "Disguised complex balance via positive algebraic geometry", arXiv:2607.04810 (2026), Theorems 8, 9, 16, 18, 20, Propositions 11, 14, Corollary 19 and Definition of the flux cone in Section 3, <https://doi.org/10.48550/arXiv.2607.04810>.
