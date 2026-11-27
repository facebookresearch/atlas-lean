# Tensor codes on the squares of a left-right Cayley complex

Let $X = \mathrm{Cay}^2(A, G, B)$ and let $C_A \subseteq \mathbb{F}_2^{A}$, $C_B \subseteq \mathbb{F}_2^{B}$ be linear codes. For a vertex $g$, the squares containing $g$ are indexed by $A \times B$, so a function $f : X(2) \to \mathbb{F}_2$ on squares restricts to a matrix $f_g \in \mathbb{F}_2^{A \times B}$. The **left-right Cayley complex code** is

$$
C[G, A, B, C_A, C_B] = \bigl\{\, f : X(2) \to \mathbb{F}_2 \;:\; f_g \in C_A \otimes C_B \text{ for every } g \in G \,\bigr\},
$$

where $C_A \otimes C_B$ is the tensor code of $A \times B$ matrices whose columns lie in $C_A$ and rows lie in $C_B$. Codewords are thus functions on squares that look locally like tensor codewords at every vertex; this is a $2$-dimensional analogue of the Tanner code of an expander graph.

## Depends on

- [Left-right Cayley complexes](left-right-cayley-complex.md)
- [Sipser-Spielman expander codes](../sipser-spielman-expander-codes.md)

## Sources

- I. Dinur, S. Evra, R. Livne, A. Lubotzky, S. Mozes, "Locally testable codes with constant rate, distance, and locality", STOC (2022), arXiv:2111.04808.
- R. M. Tanner, "A recursive approach to low complexity codes", IEEE Transactions on Information Theory 27 (1981) 533-547.
