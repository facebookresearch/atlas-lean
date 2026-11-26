# Online arborally satisfying algorithms yield online BSTs

Every online arborally satisfying algorithm $\mathcal{G}$ can be converted into an online BST algorithm whose cost on every access sequence $X$ is $O(\mathrm{cost}_{\mathcal{G}}(X) + m)$. In particular Greedy is, up to a constant factor, an online BST algorithm.

## Proof sketch

Maintain a split tree, a BST variant that supports the operations needed to realize a row of the geometric output when only the current row is known, by encoding the treap order of future touch times implicitly through a sequence of split operations; each split tree operation is simulated by $O(1)$ amortized BST rotations per output point.

## Depends on

- [Geometric Greedy (Greedy Future)](geometric-greedy.md)
- [Geometric characterization of the optimal offline BST cost](geometric-characterization-of-opt.md)

## Proof depends on

- [Geometric Greedy (Greedy Future)](geometric-greedy.md)
- [Geometric characterization of the optimal offline BST cost](geometric-characterization-of-opt.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
