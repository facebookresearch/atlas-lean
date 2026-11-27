# Identifiability of haploid single-cell 3D genome reconstruction

**Setting.** In a haploid cell each genomic locus (bead) $i \in V = \{1,\dots,n\}$ has one position $\rho(i) \in \mathbb R^d$ ($d = 3$ biologically). The data define a graph $G=(V,E)$ on the loci: backbone edges join consecutive beads, and Hi-C or microscopy data add edges (contacts) and possibly measured distances. A *framework* $(G,\rho)$ is *rigid* if, up to isometries, there are only finitely many realizations with the same edge lengths nearby, and *globally rigid* if the edge lengths determine $\rho$ uniquely up to isometry. Reconstruction is identifiable exactly when the relevant model is globally rigid.

**Contact-threshold model (negative result).** If a contact is recorded exactly when two beads are within a fixed distance, the contact matrix is the adjacency matrix of a $d$-dimensional unit ball graph. Every such graph has infinitely many unit ball realizations modulo isometries and scalings, so binary contact data alone never identify the structure. For $d=3$, $K_{1,13}$ is a minimal forbidden subgraph of unit ball graphs (kissing number $12$).

**Distances with strict inequalities.** For a generic point set satisfying given distance equalities on some pairs and *strict* distance inequalities on others, finiteness of the solution set (modulo isometries) with and without the inequalities coincides: strict inequalities never restore rigidity lost by too few distance equations.

**Global rigidity criteria.** A graph on at least $d+2$ vertices is generically globally $d$-rigid iff some (equivalently every) generic framework has an equilibrium stress whose stress matrix $\Omega$ has rank $|V| - d - 1$ (Connelly; Gortler–Healy–Thurston); a necessary condition is $|E| \ge d|V| - \binom{d+1}{2} + 1$. **Lemma (backbone powers).** If $G$ is a path (the chromosome backbone), then its $(d+1)$-th power $G^{d+1}$, joining all beads within $d+1$ steps along the backbone, is generically globally $d$-rigid; so distances between all beads at most $d+1$ apart along the chain identify the 3D structure when $d = 3$ and the beads are generic.

## Expansion

The backbone-power lemma follows by induction: $K_{d+2}$ is globally $d$-rigid and $G^{d+1}$ is built from it by adding vertices of degree $d+1$, an operation that preserves global rigidity whenever the $d+1$ neighbours affinely span $\mathbb R^d$ (true generically). The unit-ball non-uniqueness comes from perturbing, after a slight shrinking, any realization with all contact lengths strictly below threshold. The paper also derives packing-model (penny and marble graph) analogues and uses semidefinite programming for reconstruction.

## Sources

- Sean Dewar, Georg Grasegger, Kaie Kubjas, Fatemeh Mohammadi and Anthony Nixon, "Single-cell 3D genome reconstruction in the haploid setting using rigidity theory", arXiv:2407.10700 (2024), Lemmas 3.3, 3.4, 4.4 and 4.6, Proposition 4.2 and Theorem 4.5 (numbering of v1 and v2), <https://doi.org/10.48550/arXiv.2407.10700>.
