# Spherical Laughlin Fock-space operator gap

Index the occupation basis at flux $Q$ by finite subsets $A$ of $\{0,\ldots,Q\}$. The annihilator $a_j$ kills states without $j$; on a state $B$ containing $j$ it yields $B\setminus\{j\}$ with sign $(-1)^{|\{i\in B:i<j\}|}$. Put $P_p=\sum_{i<j}\sqrt2\,b_{Qp}(i,j)a_ja_i$, where $b_{Qp}(i,j)=(i-j)\sqrt{[Q]_i[Q]_j p!/(Q[2Q-2]_p i!j!)}/\sqrt2$ when $i+j=p+1$, and zero otherwise, and $[m]_k$ is the falling factorial. Let $H_Q=\sum_{0\leq p<2Q-1}P_p^*P_p$. For each real $0<\gamma<4616733319001/10^{14}$ there is an integer $Q_\gamma\geq1$ such that $H_Q^2-\gamma H_Q$ is positive semidefinite for every integer $Q\geq Q_\gamma$. The basis includes all particle numbers.

## Depends on
The signed occupation annihilators, coefficient-one pair projectors, and the finite positive-semidefinite order.

## Proof depends on
The uniform operator inequality for the sum of overlapping pair interactions, with constants below the stated threshold.

## Expansion
Expose the finite interaction matrix estimates and the threshold computation, and prove positivity uniformly over the entire occupation basis rather than just the filling-one-third sector. Do not assert that the strict spherical range includes the endpoint.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LaughlinFock.lean#L58-L61) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/269.md).
