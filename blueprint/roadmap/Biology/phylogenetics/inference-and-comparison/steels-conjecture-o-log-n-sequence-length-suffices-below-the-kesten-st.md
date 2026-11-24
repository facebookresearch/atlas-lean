# Steel's conjecture: logarithmic sequence length below the Kesten–Stigum threshold

In the Cavender–Farris–Neyman (CFN, binary symmetric) model on unrooted binary trees with $n$ leaves, an edge $e$ of length $d(e)$ carries a transition with probability $p(e) = (1 - e^{-2d(e)})/2$. Put $g^* = \ln(2)/4$ (Daskalakis, Mossel and Roch 2011, Eq. (1)). In the $\Delta$-branch model (Definition 1.1), all edge lengths are multiples of a fixed $\Delta > 0$ and satisfy $0 < f \le d(e) \le g < g^*$. Theorem 1 of the source states: there is a polynomial-time algorithm that reconstructs the tree topology from $k = c(f, g, \Delta)(\log n + \log(1/\delta))$ independent characters with error probability at most $\delta$, where $c(f, g, \Delta) = c(g)/\min\{\Delta^2, f^2\}$; and the value $g^*$ is tight. Since $1 - 2p(e) = e^{-2d(e)}$, the bound $d(e) < g^*$ is the same as $p(e) < p^* = (\sqrt2 - 1)/2^{3/2}$, the root-reconstruction threshold of the CFN model on the binary tree: the source's abstract identifies $p^*$ with the transition point for extremality of the free Gibbs measure of the Ising model on the binary tree, and Steel conjectured that $O(\log n)$ characters suffice below it.

## Expansion

1. The model: the CFN model, edge lengths and transition probabilities, the $\Delta$-branch discretization, and the parameters $f$ and $g$.
2. Root-state reconstruction below $p^*$: estimators whose error stays bounded away from $1/2$ uniformly in the depth (Section 2 of the source, after Mossel 2004).
3. The tree-building procedure that uses reconstructed ancestral sequences to estimate distances between deep vertices from $O(\log n)$ characters, while keeping the reconstructed subtrees disjoint.
4. The sample-size bound with its dependence on $f$, $g$ and $\Delta$, and the tightness of $g^*$.
5. The Jukes–Cantor analogue (Corollary 2 of the source, threshold $g^*/2$), as a separate statement.

## Sources

- C. Daskalakis, E. Mossel and S. Roch, Evolutionary trees and the Ising model on the Bethe lattice: a proof of Steel's conjecture, Probab. Theory Related Fields 149 (2011), 149–189, Definition 1.1, Eq. (1) and Theorem 1. <https://arxiv.org/abs/math/0509575>
