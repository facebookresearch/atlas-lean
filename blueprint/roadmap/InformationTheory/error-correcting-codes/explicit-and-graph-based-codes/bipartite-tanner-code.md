# Bipartite Tanner codes on regular bipartite multigraphs

Let $B$ be a $D$-regular bipartite multigraph between finite sets $L$ and $R$, presented by a bijection between left darts $L \times [D]$ and right darts $R \times [D]$, so every edge has a left port and a right port. Given local codes $C_L, C_R \subseteq \alpha^{D}$ over an alphabet $\alpha$, the bipartite Tanner code consists of all edge labellings $x : L \times [D] \to \alpha$ such that, at every left vertex, the $D$ symbols on its incident edges ordered by port lie in $C_L$, and at every right vertex they lie in $C_R$. When $C_L, C_R$ are linear, so is the Tanner code, and parity-check matrices of the local codes assemble into a parity-check matrix of row weight at most $D$.

## Depends on

- [Linear code](../linear-codes/linear-code.md)

## Sources

- R. M. Tanner, "A Recursive Approach to Low Complexity Codes", IEEE Transactions on Information Theory, 1981.
- M. Sipser, D. A. Spielman, "Expander Codes", IEEE Transactions on Information Theory, 1996.
