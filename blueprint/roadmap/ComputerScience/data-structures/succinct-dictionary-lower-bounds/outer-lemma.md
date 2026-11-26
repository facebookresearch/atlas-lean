# Outer lemma: each tree level forces linearly many probes

In the meta-operation tree for the hard distribution on $n$ keys, let $\ell$ be a level whose fanout $\lambda_{\ell+1}$ and the scheme's redundancy $R$ satisfy $m_{\ell+1} \le n/2$ and $R \le \gamma\, n \log_2 \lambda_{\ell+1}$ for a sufficiently small universal constant $\gamma > 0$. Then the expected number of probes attributed to level-$(\ell+1)$ nodes, summed over all such nodes, is at least $c \cdot n$ for a universal constant $c > 0$ (for schemes with word size $w = O(\log U + \log V)$).

## Proof sketch

Within a node, the children's segments are processed one after another; the outer communication game sends, round by round, the cells written in earlier children and probed in later ones. If few probes were attributed to the node, the inner game would make many children consistent simultaneously, and the resulting encoding of the node's inserted keys would beat their entropy minus the allowed redundancy. Markov's inequality on per-child probe counts handles children with many probes.

## Depends on

- [Meta-operation tree and probe attribution](meta-operation-tree.md)

## Proof depends on

- [Inner communication game for succinct dictionaries](inner-communication-game.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023; arXiv:2306.02253.
