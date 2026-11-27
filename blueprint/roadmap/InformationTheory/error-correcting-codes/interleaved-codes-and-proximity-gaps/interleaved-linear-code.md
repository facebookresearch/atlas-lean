# Interleaved linear codes

Let $C \subseteq M^n$ be a linear code over a ring $R$ (coordinates indexed by a finite set of size $n$) and $\kappa$ a finite index set of rows. The $\kappa$-interleaved code $C^{\kappa}$ consists of the matrices $W = (W_{i, r})$ with columns indexed by coordinates $i$ and rows by $r \in \kappa$ such that every row $i \mapsto W_{i, r}$ is a codeword of $C$. It is viewed as a code of length $n$ over the block alphabet $M^{\kappa}$, so the Hamming distance between two matrices counts the columns in which some row differs. For nonempty $\kappa$, $C^{\kappa}$ has the same minimum distance as $C$, and any linear combination of the rows of a word of $C^{\kappa}$ is a codeword of $C$.

## Depends on

- [Linear code](../linear-codes/linear-code.md)
- [Minimum distance](../linear-codes/min-dist.md)

## Sources

- E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, "Proximity Gaps for Reed-Solomon Codes", Journal of the ACM, 2023.
- V. Guruswami, A. Rudra, M. Sudan, "Essential Coding Theory", draft book, 2019.
