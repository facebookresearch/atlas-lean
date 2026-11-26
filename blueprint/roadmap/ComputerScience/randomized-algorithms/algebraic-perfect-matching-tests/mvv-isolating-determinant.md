# Isolating weights determine the minimum perfect matching through the determinant

Suppose $w$ is isolating for $G$ with unique minimum-weight perfect matching $M^*$ of weight $W$. Then $2^W$ divides $\det B$ but $2^{W+1}$ does not. Moreover, for every edge $ij$, $ij \in M^*$ if and only if $2^{W+1}$ does not divide $2^{w(i,j)} \cdot \mathrm{adj}(B)_{ji}$, where $\mathrm{adj}(B)$ is the adjugate. Hence, given an isolating weighting, $M^*$ is computed by one determinant and one adjugate (matrix inversion), which parallelize to $\mathrm{NC}$; by the isolation lemma, uniform weights in $\{1, \dots, 2|E|\}$ are isolating with probability at least $1/2$, giving a randomized parallel ($\mathrm{RNC}$) algorithm for perfect matching.

## Proof sketch

$\det B = \sum_M \pm 2^{w(M)}$ over perfect matchings; the unique minimum term $2^W$ cannot be cancelled by the others, which are multiples of $2^{W+1}$. The term $2^{w(i,j)}\mathrm{adj}(B)_{ji}$ sums $\pm 2^{w(M)}$ over the matchings containing $ij$.

## Depends on

- [The weighted Edmonds matrix of Mulmuley, Vazirani and Vazirani](weighted-edmonds-matrix.md)

## Proof depends on

- [Edmonds' theorem and the randomized bipartite matching test](edmonds-matrix-theorem.md)
- [Isolation lemma](../../../Combinatorics/probabilistic-combinatorics/isolation-lemma.md)

## Sources

- K. Mulmuley, U. V. Vazirani and V. V. Vazirani, "Matching is as Easy as Matrix Inversion", Combinatorica 7(1), 1987.
- R. Motwani and P. Raghavan, "Randomized Algorithms", Cambridge University Press, 1995.
