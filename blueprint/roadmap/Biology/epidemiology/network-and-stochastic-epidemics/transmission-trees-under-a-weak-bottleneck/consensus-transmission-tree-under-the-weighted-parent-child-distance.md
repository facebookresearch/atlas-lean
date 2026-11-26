# Consensus transmission tree under the weighted parent–child distance

Let $\Sigma$ be a finite set of hosts. A weighted transmission tree $S = (\Sigma, E)$ is a spanning arborescence on $\Sigma$ with positive integer edge weights $w : E \to \mathbb{N}_{\ge 1}$ ($w(s,t)$ = number of strains transmitted from $s$ to $t$). Extend $w$ by zero to $q_S : \Sigma \times \Sigma \to \mathbb{N}$, $q_S(s,t) = w(s,t)$ if $(s,t) \in E$ and $0$ otherwise. The **weighted parent–child distance** is

$$d(S_1, S_2) = \sum_{(s,t) \in E_1} w_1(s,t) + \sum_{(s,t) \in E_2} w_2(s,t) - 2 \sum_{(s,t) \in E_1 \cap E_2} \min\{w_1(s,t), w_2(s,t)\} = \sum_{(s,t) \in \Sigma \times \Sigma} |q_{S_1}(s,t) - q_{S_2}(s,t)|,$$

a metric on weighted transmission trees; with all weights equal to $1$ it is the size of the symmetric difference of the edge sets (the parent–child distance).

**Single consensus problem.** Given trees $S_1, \dots, S_k$, find $R$ minimizing $d(\mathcal S, R) = \sum_{i=1}^k d(S_i, R)$.

**Lemma (optimal weights for a fixed topology).** For a fixed arborescence $R$, the weights

$$w^*(s,t) = \max\{\operatorname{med}\{q_{S_1}(s,t), \dots, q_{S_k}(s,t)\},\, 1\}, \qquad (s,t) \in E(R),$$

(with the lower median when $k$ is even) minimize $d(\mathcal S, R)$.

**Theorem.** Define the complete directed graph $P$ on $\Sigma$ with (possibly negative) edge weights

$$w_P(s,t) = \sum_{i=1}^k \big(|q_{S_i}(s,t) - w^*(s,t)| - |q_{S_i}(s,t)|\big).$$

A minimum-weight spanning arborescence of $P$, weighted by $w^*$, solves the single consensus problem. Hence the consensus tree is computable in polynomial time.

## Depends on

- [Complexity of direct transmission inference](complexity-of-direct-transmission-inference.md)

## Expansion

Because $d$ is an $\ell_1$ distance on the vectors $q_S$, the cost separates over ordered host pairs. A pair that is not an edge of $R$ contributes $\sum_i |q_{S_i}(s,t)|$ regardless of $R$; a pair that is an edge contributes $\sum_i |q_{S_i}(s,t) - z|$ for the chosen weight $z \ge 1$, minimized by the median clamped to $1$. So $d(\mathcal S, R) = \sum_{(s,t)} \sum_i |q_{S_i}(s,t)| + \sum_{(s,t) \in E(R)} w_P(s,t)$, and the first sum is a constant. Minimizing over $R$ is therefore exactly a minimum-weight spanning arborescence problem on $P$, solvable by the Chu–Liu–Edmonds algorithm even with negative weights because every spanning arborescence has exactly $|\Sigma| - 1$ edges. This contrasts with the decision problem of producing a single feasible transmission tree from a phylogeny under a weak bottleneck, which is NP-complete.

## Sources

- P. Sashittal, M. El-Kebir, "Sampling and summarizing transmission trees with multi-strain infections", Bioinformatics 36 (Suppl. 1) (2020) i362–i370, Definition 5, Problem 3, Section 5.3, Lemma 1 and Theorem 3, <https://doi.org/10.1093/bioinformatics/btaa438>, PMCID PMC7355255.
