# Inner communication game for succinct dictionaries

Consider one segment of $m$ consecutive meta-operations of the hard distribution (with $m < n/2$), and two players: Alice knows the memory before the segment, Bob knows the memory after it, and both know the dictionary contents outside the segment. Call the scheme *consistent* on the segment if the cells it probes during the segment number at most $m t$ and, together with their contents in both memories, determine the segment's answers. Then the probability, over the random segment, that the scheme is consistent is at most $2^{M - H}$, where $H$ is the conditional entropy of the segment's inserted keys and values given the players' common knowledge, and $M$ is the length of a prefix-free encoding of the consistent probe transcript, which is $O(m t \log(S)) $ plus the redundancy $R$ of the scheme ($Sw \le \mathrm{OPT}(U, V, n) + R$). For update-only histories with large values ($U^{2+\alpha} \le V n^2$) a query-free version of the game gives the same form of bound.

## Proof sketch

A prefix-free message encoding the probed cells and their contents lets the receiver replay the segment and recover the inserted keys and their values. Comparing the expected message length with the conditional entropy of the segment's keys, which is about $m \log_2(n/m)$ bits beyond what the redundancy can hide, bounds the consistency probability through Kraft's inequality.

## Depends on

- [Meta-operation tree and probe attribution](meta-operation-tree.md)
- [Information-theoretic space bound for dictionaries](../hashing/succinct-dictionaries-and-hash-families/dictionary-specifications/information-theoretic-dictionary-space.md)

## Proof depends on

- [Counting bound for cell-probe trees](../cell-probe-complexity/counting-bound-for-cell-probe-trees.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023; arXiv:2306.02253.
