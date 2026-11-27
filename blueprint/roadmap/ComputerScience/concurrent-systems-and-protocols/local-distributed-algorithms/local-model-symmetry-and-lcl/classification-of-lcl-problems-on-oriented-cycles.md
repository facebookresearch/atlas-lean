# Classification of LCL problems on oriented cycles

Let $R \subseteq L \times L$ be a locally checkable labelling problem without inputs on consistently oriented cycles, with finitely many labels; a labelling $\ell$ solves $R$ if $R(\ell(v), \ell(v+1))$ for all nodes $v$. Exactly one of the following holds: (1) $R$ has a loop $R(a, a)$ and is solved in $0$ rounds; (2) $R$ has no loop but a flexible state $q$ (closed walks from $q$ to $q$ of every length at least some $K$), and its deterministic LOCAL round complexity is $\Theta(\log^* n)$; (3) $R$ has no flexible state, and its deterministic LOCAL round complexity on the cycles on which it is solvable is $\Theta(n)$ (Brandt et al. 2017, Section 4, Claim 1; Chang, Studený and Suomela, Theorem 6.1 and Lemma 6.3).

## Proof sketch

Flexible problems: compute a ruling set of anchors spaced at least $K$ apart via Cole–Vishkin, then fill each gap with a closed walk through $q$ of the right length. Inflexible problems: if an algorithm with radius $t$ succeeded on a long cycle, its outputs on long identical-looking stretches would yield closed walks of incompatible lengths through some state. Lower bounds for loop-free problems reduce to 3-colouring via Linial.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Proof depends on

- [Linial's lower bound for coloring a ring](../linial-s-lower-bound-for-coloring-a-ring.md)
- [Cole–Vishkin coloring in O(log* n) rounds](../colevishkin-coloring-in-o-log-n-rounds.md)

## Sources

- Yi-Jun Chang, Jan Studeny and Jukka Suomela, "Distributed Graph Problems Through an Automata-Theoretic Lens", Theoretical Computer Science, 2023.
- Sebastian Brandt et al., "LCL Problems on Grids", Proceedings of the ACM Symposium on Principles of Distributed Computing (PODC), 2017.
- Nathan Linial, "Locality in Distributed Graph Algorithms", SIAM Journal on Computing, 1992.
