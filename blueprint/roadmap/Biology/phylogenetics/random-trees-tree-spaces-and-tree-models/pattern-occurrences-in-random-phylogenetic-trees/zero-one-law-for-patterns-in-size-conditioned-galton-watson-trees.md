# Zero–one law for patterns in size-conditioned Galton–Watson trees

Let $X$ be a nonnegative integer-valued offspring distribution with $\mathbb E(X)=1$, $\mathbb E(X^2)<\infty$ and $\mathbb P(X=0)>0$, let $T\sim\mathrm{GW}(X)$, and let $T_n\sim(T\mid \#T=n)$ for every $n$ with $\mathbb P(\#T=n)>0$. A finite tree $\tau$ is **$X$-realizable** if it can be rooted so that all its out-degrees lie in the support of $X$. A rooted tree $T$ **contains** $\tau$, written $T\supset\tau$, if some rooting of $\tau$ is isomorphic, as a rooted tree, to a complete descendant (fringe) subtree of $T$: a vertex of $T$ together with all of its descendants, no child omitted. The source writes $T_n\supset\tau$ without fixing the convention; this one makes item 1 hold, which fails for ordinary subgraph containment (offspring $0$ or $2$ with equal probabilities, $\tau$ a single edge: neither rooting of $\tau$ has out-degrees in $\{0,2\}$, yet every three-vertex tree contains an edge).

**Theorem (0–1 law).** For every finite tree $\tau$:

1. if $\tau$ is not $X$-realizable, then $\mathbb P(T_n\supset\tau)=0$ for all $n$;
2. if $\tau$ is $X$-realizable, then $\mathbb P(T_n\supset\tau)\to 1$ as $n\to\infty$,

with $T_n\supset\tau$ the fringe containment above.

**Corollaries.** (a) If $T_n$ is uniform among $d$-ary trees with $n$ labelled leaves, then $\mathbb P(T_n\supset\tau)\to 1$ for every finite rooted $d$-ary tree $\tau$, where $T_n\supset\tau$ means that $\tau$ (leaf labels ignored) is a fringe subtree of $T_n$. (b) If $N_n$ is uniform among level-$k$ phylogenetic networks with $n$ labelled leaves, then $\mathbb P(N_n\supset\tau)\to 1$ for every finite level-$k$ network $\tau$, where $N_n\supset\tau$ means that $\tau$ (leaf labels ignored) is a pendant subnetwork of $N_n$: a vertex together with all its descendants and all edges among them, these descendants having no other parents. In particular, since tree-child networks contain no stacks (a reticulation whose only child is a reticulation) while some level-$2$ networks do, the fraction of level-$k$ networks ($k\ge 2$) that are tree-child tends to $0$.

## Proof depends on

- [Second Borel–Cantelli lemma](../../../../Probability/foundations/borel-cantelli-lemmas/second-borel-cantelli-lemma/measure-limsup-eq-one.md)

## Expansion

The proof uses the local limit of $T_n$ (Kesten's tree, Janson): an infinite spine $v_1,v_2,\dots$ in which $v_k$ receives $X_k^*-1$ extra children, $X^*$ size-biased, each extra child carrying an independent copy of $T$. Since $\tau$ is realizable, each of these independent copies is, with a fixed positive probability $p$, equal to $\tau$ rooted suitably, which gives a fringe copy of $\tau$ of height at most the diameter of $\tau$; as the number of copies grafted near the root tends to infinity, the limit contains $\tau$ in a bounded ball with probability close to $1$ by Borel–Cantelli. Local convergence transfers this to the ball of the same radius in $T_n$, and a fringe copy found there is one in $T_n$, so the limits in $n$ and in the radius can be interchanged. Conversely, a fringe copy of $\tau$ in $T_n$ has the out-degrees of $T_n$, which lie in the support of $X$, so a non-realizable $\tau$ never occurs. Uniform leaf-labelled $d$-ary trees are obtained from the critical offspring law $X\sim d\cdot\mathrm{Bernoulli}(1/d)$ conditioned on size (with a leaf grafted on the root and labels assigned uniformly), and uniform level-$k$ networks from Stufler's blow-up construction, in which pendant subnetworks correspond to fringe subtrees of the underlying Galton–Watson tree, which yields the corollaries. A pendant copy of a level-$2$ network containing a stack contains that stack.

## Sources

- F. Bienvenu and M. Steel, "0–1 laws for pattern occurrences in phylogenetic trees and networks", Bulletin of Mathematical Biology 86(8) (2024) 94, <https://doi.org/10.1007/s11538-024-01316-x>, PMCID PMC11561131. Propositions 6 and 8, Theorems 10 and 12, Corollaries 13–14 and Remark 15 (Section 3).
