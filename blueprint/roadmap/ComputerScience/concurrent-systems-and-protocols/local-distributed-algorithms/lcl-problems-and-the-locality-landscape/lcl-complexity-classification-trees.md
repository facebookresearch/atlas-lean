# Complete classification of LCL complexities on bounded-degree trees

On bounded-degree trees, the deterministic LOCAL complexity of every LCL problem is one of $O(1)$, $\Theta(\log^* n)$, $\Theta(\log n)$, or $\Theta(n^{1/k})$ for some positive integer $k$; the randomized complexity is one of these or $\Theta(\log\log n)$, and each of these classes is nonempty. The cited decision procedures cover specific problem and graph classes. For each $k \ge 2$ it is decidable on which side of the gap between $\Theta(n^{1/k})$ and $\Theta(n^{1/(k-1)})$ a given LCL on bounded-degree trees lies, while distinguishing $\Theta(1)$ from $\Theta(n)$ on bounded-degree trees is EXPTIME-hard. For LCLs on rooted regular trees given by the allowed label combinations of the children of an internal node of each label, with unconstrained leaves, an algorithm determines whether the complexity is $O(1)$, $\Theta(\log^* n)$, $\Theta(\log n)$ or $n^{\Theta(1)}$ (not the exponent), and these complexities are the same deterministically and randomly. For input-free LCLs on paths and cycles, polynomial-time-computable properties of an associated unary nondeterministic automaton determine solvability and locality, except in one case that is co-NP-complete; with input labels on paths and cycles, determining locality is PSPACE-hard.

## Proof sketch

Gap theorems are proved for each interval: $\omega(1)$ and $o(\log^* n)$ on trees by a speedup argument specific to trees, $\omega(\log^* n)$ and $o(\log n)$ by the virtual-graph speedup, and $\omega(\log n)$ and $n^{o(1)}$ by a rake-and-compress decomposition of trees into $O(\log n)$ layers, which shows that any problem solvable in $n^{o(1)}$ rounds admits a labeling of compressed paths by a finite set of types, yielding an $O(\log n)$-round algorithm. Polynomial gaps between $n^{1/k}$ and $n^{1/(k-1)}$ follow from a generalized tree decomposition and a pumping lemma for trees, and the proof yields a sequential algorithm deciding the side of each gap. For rooted regular trees, the classifier works directly on the finite problem description and may take time exponential in its size.

## Depends on

- [Deterministic and randomized LOCAL complexity of an LCL problem](lcl-deterministic-randomized-complexity.md)

## Proof depends on

- [LCL complexity gaps between constant and log-star](lcl-gap-constant-versus-log-star.md)
- [Deterministic LCL complexities between log-star and log n collapse](lcl-deterministic-gap-log-star-log-n.md)
- [A LOCAL time hierarchy: complexities n^(1/k) for every k](local-time-hierarchy-n-to-one-over-k.md)

## Sources

- Y.-J. Chang, "The Complexity Landscape of Distributed Locally Checkable Problems on Trees", DISC 2020, arXiv:2009.09645, Section 1.1 and Theorem 1.
- Y.-J. Chang, S. Pettie, "A Time Hierarchy Theorem for the LOCAL Model", FOCS 2017; SIAM Journal on Computing 48(1) (2019), arXiv:1704.06297.
- Y.-J. Chang, J. Studený, J. Suomela, "Distributed Graph Problems Through an Automata-Theoretic Lens", SIROCCO 2021; Theoretical Computer Science (2023), arXiv:2002.07659, abstract.
- A. Balliu, S. Brandt, Y.-J. Chang, D. Olivetti, J. Studený, J. Suomela, A. Tereshchenko, "Locally Checkable Problems in Rooted Trees", PODC 2021; Distributed Computing 36 (2023), arXiv:2102.09277, abstract.
- C. Grunau, V. Rozhoň, S. Brandt, "The Landscape of Distributed Complexities on Trees and Beyond", PODC 2022, arXiv:2202.04724, abstract.
