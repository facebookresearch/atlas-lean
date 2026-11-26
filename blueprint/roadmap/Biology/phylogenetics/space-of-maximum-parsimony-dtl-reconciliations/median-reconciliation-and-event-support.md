# Median reconciliation and event support

Let $\mathcal R$ be a finite set of reconciliations of the same gene tree $G$ and species tree $S$, each identified with its set $E(R)$ of events (two events are identified when they assign the same gene node to the same species node with the same event type and child placement). For $e \in \bigcup_R E(R)$ let the **support** $f(e)$ be the fraction of $R \in \mathcal R$ with $e \in E(R)$. Define the asymmetric and symmetric distances

$$d_a(R_1, R_2) = |E(R_2) \setminus E(R_1)|, \qquad d_s(R_1, R_2) = |E(R_1) \oplus E(R_2)| .$$

An **asymmetric (symmetric) median reconciliation** is an $R \in \mathcal R$ minimizing $\sum_{R' \in \mathcal R} d_a(R, R')$ (respectively $\sum_{R' \in \mathcal R} d_s(R, R')$).

**Lemma 1.** An asymmetric median reconciliation is a reconciliation $R \in \mathcal R$ maximizing $\sum_{e \in E(R)} f(e)$, and a symmetric median reconciliation is one maximizing $\sum_{e \in E(R)} \big(f(e) - \tfrac12\big)$.

**Theorems 1 and 2.** When $\mathcal R$ is the set of all canonical MPRs of a dated species tree (in the time-subdivided DTL model), represented by its reconciliation graph (DTL-graph) with event supports precomputed, a single bottom-up pass that keeps, at each mapping node, the event child of largest accumulated support, followed by a top-down backtrack, returns an MPR maximizing the total event support. It runs in time linear in the size of the graph, hence polynomially in $|G|$ and $|S|$, although there may be exponentially many MPRs. Subtracting $\tfrac12$ from every support first yields the symmetric median.

Unlike majority-rule consensus trees, the events with support above $\tfrac12$ need not be realizable together in one reconciliation; the median is the realizable reconciliation carrying the most support. Supports can also be averaged over near-optimal reconciliations obtained by perturbing event costs, and events below a support threshold filtered as unreliable.

## Depends on

- [Reconciliation graph of maximum parsimony DTL reconciliations](reconciliation-graph-of-maximum-parsimony-reconciliations.md)

## Expansion

With $N = |\mathcal R|$, $\sum_{R'} |E(R') \setminus E(R)| = \sum_{R'} |E(R')| - N \sum_{e \in E(R)} f(e)$, and the first term does not depend on $R$. Likewise $\sum_{R'} |E(R) \oplus E(R')| = \sum_{R'} |E(R')| + \sum_{e \in E(R)} N\,(1 - 2 f(e))$, which is minimized by maximizing $\sum_{e \in E(R)} (f(e) - \tfrac12)$. A traversal of the reconciliation graph picks one event child per mapping node and all mapping children of an event, so the maximum total support is a max-plus dynamic program over the acyclic graph.

## Sources

- T.-H. Nguyen, V. Ranwez, V. Berry, C. Scornavacca, "Support measures to estimate the reliability of evolutionary events predicted by reconciliation methods", PLoS ONE 8(10):e73667 (2013), Eqs. (1)-(2), Problems 1-2, Lemma 1, Theorems 1 and 2 and Algorithm 1, <https://doi.org/10.1371/journal.pone.0073667>, PMCID PMC3790797.