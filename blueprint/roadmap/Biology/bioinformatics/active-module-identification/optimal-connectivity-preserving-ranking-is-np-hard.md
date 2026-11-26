# Optimal connectivity-preserving ranking is NP-hard

A ranking $v_1, \dots, v_n$ of the vertices of a graph $G$ is connectivity preserving if for every $k$ the subgraph induced by $\{v_1, \dots, v_k\}$ is connected. The optimal connectivity-preserving ranking problem takes $G$ and probabilities $p_i$ on its vertices and asks for a connectivity-preserving ranking maximizing the [expected AUC](expected-auc-of-a-ranking-under-posterior-membership-probabilities.md), equivalently minimizing $\sum_i i\,p_{v_i}$. This problem is NP-hard: its decision version (is there a connectivity-preserving ranking with $\sum_i i\,p_{v_i} \le k$?) has a yes-answer exactly when a corresponding instance of exact cover by 3-sets has an exact cover.

## Depends on

- [Expected AUC of a ranking under posterior membership probabilities](expected-auc-of-a-ranking-under-posterior-membership-probabilities.md)

## Expansion

The reduction builds a graph with a root vertex $v$, one vertex $c_i$ per 3-set and one vertex per ground element joined to the vertices of the sets containing it, with probabilities chosen so that element vertices carry the weight but are reachable only through set vertices. An exact cover yields the ranking root, $c_1$, its three elements, $c_2$, its three elements, and so on, meeting the bound; conversely any ranking meeting the bound must reveal three new elements after each of the first $q$ set vertices, which is an exact cover. Because of this hardness, the source uses a greedy heuristic that repeatedly removes the vertex whose removal detaches the subgraph of highest average false discovery rate and assigns it the lowest remaining ranks.

## Sources

- N. Alexeev, J. Isomurodov, V. Sukhov, G. Korotkevich and A. Sergushichev, "Markov chain Monte Carlo for active module identification problem", BMC Bioinformatics 21 (Suppl. 6) (2020) 261, <https://doi.org/10.1186/s12859-020-03572-9>, PMCID PMC7672893. Definition 1, Problem 2, Lemma 2 and Proposition 1 (Appendix S2).
