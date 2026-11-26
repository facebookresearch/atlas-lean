# Electrostatic persistence via a charge-weighted sigmoid filtration

For atoms $i, j$ at distance $d_{ij} > 0$ with partial charges $q_i, q_j$, and a nonzero parameter $c$, define

$$\Phi(d_{ij}, q_i, q_j; c) = \frac{1}{1 + \exp(-c\, q_i q_j / d_{ij})} .$$

Then $\Phi \in (0, 1)$; $\Phi = 1/2$ exactly when $q_i q_j = 0$, and $\Phi \to 1/2$ as $d_{ij} \to \infty$; for $c > 0$, like charges ($q_i q_j > 0$, repulsive) give $\Phi \in (1/2, 1)$ and opposite charges ($q_i q_j < 0$, attractive) give $\Phi \in (0, 1/2)$, with the roles exchanged for $c < 0$. Using $\Phi$ as the filtration value of the pair $(i, j)$, combined with the interactive mask between protein and ligand atoms, the $0$-dimensional barcodes of the resulting Rips filtration encode the charge–distance pattern of electrostatic interactions across the interface (electrostatic persistence).

## Depends on

- [Bond-masked and interactive distance matrices for Rips filtrations](bond-masked-and-interactive-distance-matrices.md)

## Expansion

The value is the logistic function of $c\, q_i q_j / d_{ij}$, a Coulomb-like interaction energy up to scale, so its sign and magnitude are monotone in that energy and the sigmoid squashes it into the unit interval where a fixed filtration range applies; $c$ is chosen to spread the observed values over $(0, 1)$ for learning rather than for physical meaning. With $c > 0$, strongly attractive pairs enter the filtration first, so the earliest-connecting atoms are those in salt-bridge-like contacts. An alternative charge correlation $q_i q_j e^{-d_{ij}/\eta_{ij}}$ and a charge density $\mu_c(r) = \sum_j q_j e^{-\lVert r - r_j \rVert / \eta_j}$ give different filtration domains for the same information.

## Sources

- Cang Z, Mu L, Wei GW. Representability of algebraic topology for biomolecules in machine learning based scoring and virtual screening. *PLoS Computational Biology* 14:e1005929 (2018), Methods, "Persistent homology", "Element specific persistent homology" and "Distance matrix induced persistent homology", equations (3)–(10). DOI <https://doi.org/10.1371/journal.pcbi.1005929>. PMCID PMC5774846.
