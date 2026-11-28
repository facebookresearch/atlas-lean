# Integer linear program for cluster-level data splitting

**Setting.** An instance of the $(k, R, C)$-DataSAIL problem: data elements $\mathcal D$ with entity types $t$, cardinalities $\kappa$, classes $\sigma$, similarity $\mathrm{sim}$, split fractions $s_i$ and tolerances $\epsilon, \delta$; the goal is a split $\pi : \mathcal D \to [k]$ minimizing the leakage $L(\pi) = \sum_{\{x, x'\}} [\pi(x) \ne \pi(x')]\,\mathrm{sim}(x, x')\,\kappa(x)\kappa(x')$ under the size and stratification constraints.

**ILP (Eqs. (12)–(18)).** Use binary variables $\xi_{x,i}$ ($x$ is in fold $i$) and $\zeta_{xx'}$ for unordered pairs ($x$ and $x'$ are in different folds), and write $w_{xx'} = \mathrm{sim}(x, x')\,\kappa(x)\,\kappa(x')$:

$$\min_{\xi, \zeta} \sum_{\{x, x'\} \in \binom{\mathcal D}{2}} w_{xx'}\, \zeta_{xx'}$$

subject to

$$\sum_{i=1}^{k} \xi_{x,i} = 1 \ (x \in \mathcal D), \qquad \sum_{t(x) = r} \kappa(x)\, \xi_{x,i} \ge (1 - \epsilon)\, s_i\, n_r, \qquad \sum_{t(x) = r,\ c \in \sigma(x)} \kappa(x)\, \xi_{x,i} \ge (1 - \delta)\, s_i\, n_r^c,$$

$$\zeta_{xx'} \ge \xi_{x,i} - \xi_{x',i} \quad \text{for all } \{x, x'\} \text{ and } i \in [k], \qquad \xi_{x,i}, \zeta_{xx'} \in \{0, 1\}.$$

**Claim.** If all similarities are nonnegative, the ILP is equivalent to $(k, R, C)$-DataSAIL: at an optimum $\zeta_{xx'} = [\pi_\xi(x) \ne \pi_\xi(x')]$ for every pair with $w_{xx'} > 0$, so the objective equals $L(\pi_\xi)$, and setting $\zeta$ to the separation indicator on the remaining pairs gives an optimum satisfying Eq. (19) for all pairs. It has $O(|\mathcal D| k + |\mathcal D|^2)$ variables and $O(kRC + |\mathcal D|^2 k)$ constraints, hence constant size when $\mathcal D$ is a constant number of clusters.

**Cluster reduction.** Cluster the elements of each entity type into $K$ clusters, treat each cluster $A$ as one element with $\kappa_{\mathcal C}(A) = \sum_{x \in A} \kappa(x)$, per-class cardinalities $\kappa^c_{\mathcal C}(A) = \sum_{x \in A,\ c \in \sigma(x)} \kappa(x)$ used in place of $\kappa$ in the stratification constraints, and a linkage similarity $\mathrm{sim}_{\mathcal C}$ (similarities between clusters of different types set to $0$), solve the constant-size ILP, and unpack by $\pi(x) = \pi_{\mathcal C}(A)$ for $x \in A$. Because cardinalities add, the unpacked split satisfies the same size constraints as the cluster split, and, with the per-class cardinalities, the same stratification constraints. (With a single class set per cluster, such as the union of its members' classes, the stratification constraints are not preserved; the source claims both without this refinement.) For two-dimensional data (drug-target pairs), a measured pair is assigned to fold $i$ only if both of its entities are in fold $i$ and is discarded otherwise.

## Depends on

- [NP-hardness of leakage-minimizing data splitting](np-hardness-of-leakage-minimizing-data-splitting.md)

## Expansion

Constraint $\sum_i \xi_{x,i} = 1$ makes $\xi$ encode a map $\pi_\xi$. If $x$ and $x'$ share a fold, every right-hand side $\xi_{x,i} - \xi_{x',i}$ is $0$; otherwise it equals $1$ for the fold containing $x$ but not $x'$. Since the objective has nonnegative coefficients, minimization drives $\zeta_{xx'}$ down to that lower bound, the separation indicator, whenever $w_{xx'} > 0$; for $w_{xx'} = 0$ the value of $\zeta_{xx'}$ does not affect the objective. The source prints the objective weight as $\mathrm{sim}(x, x')$; for elementary data points ($\kappa \equiv 1$) this coincides with $w_{xx'}$, With clusters as elements and $w = \mathrm{sim}_{\mathcal C}\,\kappa_{\mathcal C}\kappa_{\mathcal C}$, the cluster objective equals the leakage of the unpacked split exactly when $\mathrm{sim}_{\mathcal C}(A, A') = \sum_{x \in A,\, x' \in A'} \mathrm{sim}(x,x')\kappa(x)\kappa(x')/(\kappa_{\mathcal C}(A)\kappa_{\mathcal C}(A'))$, the $\kappa$-weighted average linkage; with single or complete linkage (also offered by the source) the objective only bounds the unpacked leakage from above or below.

The reduction trades optimality for tractability: the exact problem is NP-hard, while a $K$-cluster instance has a bounded number of variables independent of the dataset size. Splits computed this way keep similar sequences or scaffolds in the same fold, so test performance measures generalization to dissimilar molecules rather than recall of near-duplicates.

## Sources

- R. Joeres, D. B. Blumenthal, O. V. Kalinina, "Data splitting to avoid information leakage with DataSAIL", Nature Communications 16 (2025), Eqs. (12)–(19), sections "An integer linear programming formulation of the (r, R, C)-DataSAIL problem" and "Implementation details", <https://doi.org/10.1038/s41467-025-58606-8>, PMCID PMC11978981.
