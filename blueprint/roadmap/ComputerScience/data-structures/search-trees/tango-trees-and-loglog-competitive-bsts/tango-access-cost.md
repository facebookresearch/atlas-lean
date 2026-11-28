# Cost of a tango-tree access

If serving the access $x_t$ changes $k_t$ preferred children, the tango tree serves it with $O((k_t + 1)(1 + \log \log n))$ BST operations (touched nodes and rotations).

## Proof sketch

Each auxiliary tree stores at most $O(\log n)$ keys, so searching, splitting and concatenating it costs $O(\log\log n)$. The access visits the auxiliary trees of the $k_t + 1$ preferred paths it crosses, and at each crossing performs a constant number of cuts and joins located by the depth augmentation.

## Depends on

- [Tango trees](tango-tree.md)
- [Preferred children and preferred paths](preferred-paths.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Mihai Pătraşcu, "Dynamic Optimality—Almost", SIAM Journal on Computing 37(1) (2007); FOCS (2004).
