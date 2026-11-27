# Boundary steady states lie on siphon faces

Let $G$ be a chemical reaction network on species $c_1,\dots,c_s$ with complexes $c^{y_1},\dots,c^{y_n}$ (monomials) and mass-action dynamics $\dot c=\sum_{c^{y_i}\to c^{y_j}}\kappa_{ij}c^{y_i}(y_j-y_i)$ with rate constants $\kappa_{ij}>0$. A nonempty $Z\subseteq[s]$ is a **siphon** if for every $z\in Z$ and every reaction $c^{y_i}\to c^{y_j}$ whose product complex contains $c_z$, the reactant complex $c^{y_i}$ contains some $c_a$ with $a\in Z$. Being a siphon does not depend on the rate constants. Let $\mathfrak P_Z=\langle c_a:a\in Z\rangle$.

1. $Z$ is a siphon if and only if the face $V_{\ge0}(\mathfrak P_Z)=\{c\ge0:c_a=0\ \forall a\in Z\}$ is forward invariant for the mass-action system.
2. If $\gamma\in\partial\mathbb R^s_{\ge0}$ is a boundary steady state, its zero set $Z=\{i:\gamma_i=0\}$ is a siphon.
3. If $G$ is strongly connected, then $\gamma\in\mathbb R^s_{\ge0}$ is a boundary steady state if and only if its zero set is a siphon.
4. For a toric (complex-balanced) dynamical system with positive initial condition $c^{(0)}$, a face $F_Z$ of the invariant polyhedron $\mathcal P_{c^{(0)}}=(c^{(0)}+\text{stoichiometric subspace})\cap\mathbb R^s_{\ge0}$ contains a steady state in its relative interior if and only if $Z$ is a siphon.

So checking whether given initial concentrations admit boundary steady states comes down to deciding which siphons meet the corresponding stoichiometric compatibility class.

## Proof sketch

If $c_a=0$ for all $a\in Z$, then a species in $Z$ can only be produced by reactions whose reactant complex vanishes. The siphon condition says exactly that all such production terms are zero, which gives invariance. At a boundary steady state, every reaction producing a zero species must have zero flux, so its reactant complex contains a zero species. For strongly connected networks the converse uses the fact that every complex with a vanishing monomial can be chained back through the network.

## Sources

- Anne Shiu and Bernd Sturmfels, "Siphons in Chemical Reaction Networks", *Bulletin of Mathematical Biology* 72 (2010), 1448–1463, <https://doi.org/10.1007/s11538-010-9502-y>. Preprint version: arXiv:0904.4529 (2009), Section 2 (definition of siphon, Proposition 2.1, Lemmas 2.2–2.4); published in Bulletin of Mathematical Biology 72 (2010), <https://doi.org/10.48550/arXiv.0904.4529>.
