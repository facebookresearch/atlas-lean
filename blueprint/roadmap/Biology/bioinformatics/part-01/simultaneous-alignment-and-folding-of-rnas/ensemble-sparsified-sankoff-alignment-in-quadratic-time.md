# Ensemble-sparsified Sankoff alignment in quadratic time

Let $A$ and $B$ be RNA sequences of lengths $n$ and $m$. A *structure alignment triple* $(S, T, \mathcal A)$ consists of secondary structures $S$ of $A$ and $T$ of $B$ and an alignment $\mathcal A$ of $A$ and $B$ under which matched base pairs are compatible. Sankoff's simultaneous alignment and folding maximizes a combined score, here loop-based lightweight energy contributions plus alignment similarity and gap costs, over all triples. Exact evaluation of Sankoff's recursion takes $O(n^3 m^3)$ time, and the PMcomp-style lightweight version $O(n^2 m^2)$.

From the Boltzmann ensemble of each sequence (computable by an extension of McCaskill's algorithm in the same complexity), define for $A$:
- $\Pr[(i,j) \mid A]$, the probability that $(i,j)$ is a base pair;
- $\Pr[k \in \mathrm{loop}(i,j) \mid A]$, the probability that $(i,j)$ is paired (or is the pseudo pair closing the external loop) and $k$ is unpaired in the loop it closes;
- $\Pr[(i',j') \in \mathrm{loop}(i,j) \mid A]$, the analogous probability for an inner base pair $(i',j')$ directly enclosed by $(i,j)$;

and similarly for $B$. Fix thresholds $\theta_1, \theta_2, \theta_3 \in (0, 1]$. A triple is *sparse* if:
- (C1) every base pair $a \in S$ and $b \in T$ has $\Pr[a \mid A] \ge \theta_1$, $\Pr[b \mid B] \ge \theta_1$;
- (C2) every matched pair $(i,k) \in \mathcal A$ of unpaired internal bases has $\Pr[i \in \mathrm{loop}(\hat a) \mid A] \ge \theta_2$ and $\Pr[k \in \mathrm{loop}(\hat b) \mid B] \ge \theta_2$, where $\hat a, \hat b$ are their parent pairs in $S, T$;
- (C3) every internal base pair $a \in S$, $b \in T$ has $\Pr[a \in \mathrm{loop}(\hat a) \mid A] \ge \theta_3$ and $\Pr[b \in \mathrm{loop}(\hat b) \mid B] \ge \theta_3$.

**Theorem.** The best-scoring sparse structure alignment triple can be computed in $O(nm)$ time and space.

## Depends on

- [Weight of a secondary structure](../../mccaskill-partition-function-for-rna-folding/weight.md)

## Expansion

The recursion keeps, for each pair of candidate base pairs $(a,b)$, a matrix $M^{ab}$ of best scores for aligning the loop interiors. A position $i$ is *represented* for $a$ if it satisfies (C2) for $a$ or ends an inner pair satisfying (C3). An unrepresented entry of $M^{ab}$ can only be reached through gaps. It therefore equals $M^{ab}(i^*, k^*) + (i - i^*)\gamma + (k - k^*)\gamma$, where $i^*, k^*$ are the nearest represented predecessors and $\gamma$ is the gap cost, so it need not be stored. For the complexity, the events "$i$ is unpaired in the loop of $a$" (or ends a pair directly in the loop of $a$) are disjoint over $a$. Their probabilities sum to at most $1$, and each represented one is at least $\min(\theta_2, \theta_3)$, so each position is represented for at most $1/\min(\theta_2,\theta_3)$ base pairs. Condition (C1) likewise bounds the base pairs starting at a position by $1/\theta_1$, so each entry is filled in constant time. Summing the products of these constant counts over all position pairs $(i,k)$ gives $O(nm)$ entries in total. Without (C2) and (C3), the same count gives $O(n^2 m^2)$. Unlike sequence-alignment heuristics, the sparsification depends only on the structure ensembles, and loop insertions and deletions remain allowed.

## Sources

- S. Will, C. Otto, M. Miladi, M. Möhl, R. Backofen, "SPARSE: quadratic time simultaneous alignment and folding of RNAs without sequence-based heuristics", *Bioinformatics* (2015), Section 3.3 (ensemble probabilities, Definitions 2–3, Lemma 1) and Section 3.3.3 (complexity analysis and Theorem 1), <https://doi.org/10.1093/bioinformatics/btv185> (PMC4514930).
