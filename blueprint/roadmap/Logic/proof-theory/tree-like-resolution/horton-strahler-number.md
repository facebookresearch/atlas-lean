# Horton–Strahler number of a tree-like derivation

The *Horton–Strahler number* $\mathrm{hs}(T)$ of a binary tree $T$ is defined recursively: a leaf has $\mathrm{hs} = 0$; a node with children of numbers $a$ and $b$ has $\mathrm{hs} = \max(a, b)$ if $a \ne b$ and $a + 1$ if $a = b$. It equals the height of the largest complete binary tree that embeds in $T$ (as a topological minor), and $T$ has at least $2^{\mathrm{hs}(T)+1} - 1$ nodes.

## Depends on

- [Tree-like resolution derivation](../../propositional-logic/resolution-size-and-width/resolution-tree.md)

## Sources

- J. L. Esteban and J. Torán, "Space Bounds for Resolution", Information and Computation 171(1), 84–97, 2001: proof of Theorem 7 (the depth $d_c$ of the largest embedded complete binary tree).
- J. Torán, "Space and Width in Propositional Resolution", Bulletin of the EATCS 83, 86–104, 2004.
