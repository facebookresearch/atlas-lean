# NP-hardness of leakage-minimizing data splitting

**Setting.** Let $\mathcal D$ be a finite set of data elements (biomolecules such as proteins, compounds or sequences, or clusters of them), each with an entity type $t(x) \in [R] = \{1, \dots, R\}$ (for drug-target interaction data $R = 2$: drugs and targets), a cardinality $\kappa(x) \in \mathbb N_{\ge 1}$ ($\kappa(x) = 1$ for an elementary data point), and a set of classes $\sigma(x) \subseteq [C]$. Let $\mathrm{sim} : \mathcal D \times \mathcal D \to \mathbb R$ be a similarity. Write $n_r = \sum_{t(x) = r} \kappa(x)$ and $n_r^c = \sum_{t(x) = r,\, c \in \sigma(x)} \kappa(x)$. A split into $k$ folds is a map $\pi : \mathcal D \to [k]$ with folds $\mathcal D_i^\pi = \pi^{-1}(i)$.

**Leakage.** The information leakage of $\pi$ is the total similarity between elements placed in different folds,

$$L(\pi) = \sum_{\{x, x'\} \in \binom{\mathcal D}{2}} [\pi(x) \ne \pi(x')]\, \mathrm{sim}(x, x')\, \kappa(x)\, \kappa(x').$$

**The $(k, R, C)$-DataSAIL problem.** Given split fractions $s_1, \dots, s_k \in (0, 1)$ with $\sum_i s_i = 1$ and tolerances $\epsilon \in [0, 1)$, $\delta \in [0, 1]$, minimize $L(\pi)$ subject to the size constraints

$$\sum_{x \in \mathcal D_i^\pi,\ t(x) = r} \kappa(x) \ge (1 - \epsilon)\, s_i\, n_r \quad \text{for all } (i, r) \in [k] \times [R],$$

and the stratification constraints

$$\sum_{x \in \mathcal D_i^\pi,\ t(x) = r,\ c \in \sigma(x)} \kappa(x) \ge (1 - \delta)\, s_i\, n_r^c \quad \text{for all } (i, r, c) \in [k] \times [R] \times [C].$$

**Theorem 1.** For all fixed $k \ge 2$, $R \ge 1$ and $C \ge 1$, the $(k, R, C)$-DataSAIL problem is NP-hard.

## Expansion

The proof chains three polynomial reductions.

1. *Classes.* From $(k, R, 1)$ to $(k, R, C)$: assign the elements to the $C$ classes arbitrarily and set $\delta = 1$, which makes the stratification constraints vacuous, so feasible and optimal splits coincide.
2. *Entity types.* From $(k, 1, 1)$ to $(k, R, 1)$: make $R$ copies $x_1, \dots, x_R$ of every element with the same cardinalities, give copies of the same element similarity $M = R^2 \sum_{\{x, x'\}} \mathrm{sim}(x, x')$ and copy pairs of distinct elements their original similarity. Lifting a split by $\pi_R(x_r) = \pi_1(x_1)$ multiplies every cut edge by $\binom{R}{2} + R$, so $\mathrm{OPT}_R \le (\binom{R}{2} + R)\,\mathrm{OPT}_1 < M$. Any split separating two copies costs at least $M$, so an optimum keeps copies together and projects to a split of cost $\mathrm{OPT}_R/(\binom{R}{2} + R) \le \mathrm{OPT}_1$, which is therefore optimal.
3. *Base case.* From minimum $k$-section, NP-hard even on balanced instances with $|V| = kC'$: take $\mathcal D = V$, $\kappa \equiv 1$, $\mathrm{sim}(x, x') = [xx' \in E]$, $s_i = 1/k$ and $\epsilon = 0$. The size constraints force all folds to have $|V|/k$ elements and $L(\pi)$ is the number of cut edges.

For $k = 2$ the base case is minimum graph bisection. The hardness motivates the heuristic of solving the problem exactly only on a constant number of precomputed clusters (see the integer linear program for cluster-level splitting).

## Sources

- R. Joeres, D. B. Blumenthal, O. V. Kalinina, "Data splitting to avoid information leakage with DataSAIL", Nature Communications 16 (2025), Eqs. (2)–(6), Theorem 1 and section "Proof of Theorem 1" (Eqs. (7)–(11)), <https://doi.org/10.1038/s41467-025-58606-8>, PMCID PMC11978981.
