# The tree-structure bottleneck for succinct dynamic dictionaries

A dynamic rank/select dictionary is said to hit the *tree-structure bottleneck* if it maintains an explicit dynamic balanced search tree (or a comparable pointer-based hierarchy) over $\tilde{\Theta}(n)$ blocks, so that encoding the shape and the separator data of the tree alone costs $\tilde{\Omega}(n)$ bits of redundancy. Prior dynamic rank/select structures with $O(1 + \log n / \log\log U)$ time all hit this bottleneck, and whether redundancy $o(n)$ is achievable was asked by Pibiri and Venturini.

## Depends on

- [Dynamic ordered dictionary with rank and select](dynamic-ordered-dictionary-with-rank.md)

## Sources

- William Kuszmaul, Jingxun Liang, Renfei Zhou, "Succinct Dynamic Rank/Select: Bypassing the Tree-Structure Bottleneck", SODA (2026), arXiv:2510.19175.
