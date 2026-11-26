# Complete classification of LCL complexities on bounded-degree trees

On bounded-degree trees, the deterministic LOCAL complexity of every LCL problem is one of $O(1)$, $\Theta(\log^* n)$, $\Theta(\log n)$, or $\Theta(n^{1/k})$ for some positive integer $k$; the randomized complexity is one of these or $\Theta(\log\log n)$. Each of these classes is nonempty, and for problems without inputs on bounded-degree rooted trees and on paths and cycles the class of a given LCL can be decided algorithmically.

## Proof sketch

Gap theorems are proved for each interval: $\omega(1)$ and $o(\log^* n)$ by Naor–Stockmeyer, $\omega(\log^* n)$ and $o(\log n)$ by the virtual-graph speedup, and $\omega(\log n)$ and $n^{o(1)}$ by a rake-and-compress decomposition of trees into $O(\log n)$ layers, which shows that any problem solvable in $n^{o(1)}$ rounds admits a labeling of compressed paths by a finite set of types, yielding an $O(\log n)$-round algorithm. Polynomial gaps between $n^{1/(k+1)}$ and $n^{1/k}$ follow from a refined type analysis of the decomposition.

## Depends on

- [Deterministic and randomized LOCAL complexity of an LCL problem](lcl-deterministic-randomized-complexity.md)

## Proof depends on

- [No LCL complexities between constant and log-star](lcl-gap-constant-versus-log-star.md)
- [Deterministic LCL complexities between log-star and log n collapse](lcl-deterministic-gap-log-star-log-n.md)
- [A LOCAL time hierarchy: complexities n^(1/k) for every k](local-time-hierarchy-n-to-one-over-k.md)

## Sources

- Y.-J. Chang, "The Complexity Landscape of Distributed Locally Checkable Problems on Trees", DISC 2020.
- Y.-J. Chang, S. Pettie, "A Time Hierarchy Theorem for the LOCAL Model", FOCS 2017; SIAM Journal on Computing 48(1) (2019), arXiv:1704.06297.
- Y.-J. Chang, J. Studený, J. Suomela, "Distributed Graph Problems Through an Automata-Theoretic Lens", SIROCCO 2021; Theoretical Computer Science (2023), arXiv:2002.07659.
