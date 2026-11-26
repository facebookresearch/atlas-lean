# Bond-masked and interactive distance matrices for Rips filtrations

Let $M = (M_{ij})$ be a distance matrix on the atoms of a molecule or complex, let $D(i, j)$ be the number of covalent bonds on a shortest bond path from atom $i$ to atom $j$, and let $d_\infty$ exceed the largest filtration value used. The $n$-th level matrix is

$$\tilde M^{n}_{ij} = \begin{cases} d_\infty, & D(i, j) \le n, \\ M_{ij}, & \text{otherwise}, \end{cases}$$

(with $\tilde M^{1}$ masking exactly the bonded pairs), and for a partition $A = A_1 \cup A_2$ of the atoms (for example protein and ligand) the interactive matrix is

$$\hat M_{ij} = \begin{cases} M_{ij}, & a_i \in A_1, a_j \in A_2 \text{ or } a_i \in A_2, a_j \in A_1, \\ d_\infty, & \text{otherwise}. \end{cases}$$

In the Rips filtration of $\tilde M^{n}$ no edge between atoms within $n$ bonds of each other ever appears, so the $0$-dimensional bars record non-covalent contacts at bond separation greater than $n$; in the Rips filtration of $\hat M$ every edge joins $A_1$ to $A_2$, so the $0$-dimensional bars record only cross-interface contacts. A kernel version replaces $M_{ij}$ by $1 - \Phi(d_{ij}; \eta_{ij}, \nu)$ with the generalized Lorentz kernel $\Phi(d; \eta, \nu) = 1/(1 + (d/\eta)^{\nu})$, whose row sums $\mu_i = \sum_j \Phi(d_{ij}; \eta_{ij}, \nu)$ are the flexibility–rigidity indices.

## Depends on

- [Persistent homology barcodes of a Vietoris–Rips filtration](persistent-homology-barcodes-of-a-rips-filtration.md)

## Expansion

An entry equal to $d_\infty$ is never reached by the filtration, so the corresponding edge is simply absent; the modified matrices may violate the triangle inequality, which the Rips construction does not need. For a small ligand the ordinary barcodes are almost all short $\beta_0$ bars equal to bond lengths, identical for two slightly different conformations; masking bonded pairs produces new $\beta_0$, $\beta_1$ and $\beta_2$ features driven by hydrogen bonds and van der Waals contacts that do distinguish the conformations. The interactive matrix applied to protein–ligand complexes characterizes the binding interface at different contact distances, and the same construction applies to a mutation site against its surrounding residues.

## Sources

- Cang Z, Mu L, Wei GW. Representability of algebraic topology for biomolecules in machine learning based scoring and virtual screening. *PLoS Computational Biology* 14:e1005929 (2018), Methods, "Persistent homology", "Element specific persistent homology" and "Distance matrix induced persistent homology", equations (3)–(10). DOI <https://doi.org/10.1371/journal.pcbi.1005929>. PMCID PMC5774846.
