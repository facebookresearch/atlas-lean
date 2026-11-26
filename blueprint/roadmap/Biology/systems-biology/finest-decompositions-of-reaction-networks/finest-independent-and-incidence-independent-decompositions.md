# Finest independent and incidence-independent decompositions

**Setting.** A reaction network $\mathcal N$ has $n$ complexes, $\ell$ linkage classes, stoichiometric subspace $S\subseteq\mathbb R^m$ of dimension $s$, and deficiency $\delta=n-\ell-s$. A decomposition $\mathcal N=\mathcal N_1\cup\dots\cup\mathcal N_k$ partitions the reactions; $\mathcal N_i$ has $n_i$ complexes, $\ell_i$ linkage classes, stoichiometric subspace $S_i$ and deficiency $\delta_i$. The decomposition is

- **independent** if $S=S_1\oplus\dots\oplus S_k$;
- **incidence-independent** if the image of the incidence map is the direct sum of the images of the subnetwork incidence maps, equivalently $n-\ell=\sum_i(n_i-\ell_i)$;
- **bi-independent** if it is both.

**Uniqueness of the finest decompositions.** Every finite set of reaction vectors has exactly one independent decomposition with no independent refinement, the finest independent decomposition (FID), and exactly one incidence-independent decomposition with no incidence-independent refinement, the finest incidence-independent decomposition (FIID).

**Deficiency bookkeeping.** For an independent decomposition $\delta\le\sum_i\delta_i$, and for an incidence-independent one $\delta\ge\sum_i\delta_i$; a decomposition is bi-independent iff $\delta=\sum_i\delta_i$.

**Characterizations.** The following are equivalent for a network: (i) its FID is bi-independent; (ii) every independent decomposition is bi-independent; (iii) $\delta=\sum_i\delta_i$ for every independent decomposition. Moreover, for every deficiency-zero network the FID equals the FIID, and a network has deficiency zero iff its FID is a zero-deficiency decomposition (all $\delta_i=0$).

**Equilibria.** If a mass-action system satisfies $\delta=\delta_1+\dots+\delta_\ell$ over its linkage classes, it has a positive equilibrium iff every linkage-class subsystem does.

## Expansion

The finest decompositions come from the matroid of the reaction vectors: an independent decomposition is a partition into unions of connected components of the linear matroid of reaction vectors, so the finest one is unique; the same argument on the incidence vectors gives the FIID. The inequalities follow from $\dim\bigoplus S_i\ge\dim S$ with equality iff independent, together with $\sum(n_i-\ell_i)\ge n-\ell$ with equality iff incidence-independent. For deficiency zero, $s=n-\ell$, which forces both direct sums simultaneously. Independence makes the positive equilibrium set the intersection of the subnetwork equilibrium sets (Feinberg), so equilibria can be computed block by block.

## Sources

- B. S. Hernandez, J. P. C. Santos, P. V. N. Lubenia, E. R. Mendoza, "The finest decompositions' architecture of a reaction network", arXiv:2412.15225 (2024), Theorems 3.2, 3.10 and 4.5, Propositions 4.2 and 4.8, Corollary 4.6, Theorem 5.1, <https://doi.org/10.48550/arXiv.2412.15225>.
