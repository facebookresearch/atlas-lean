# The local tester of a left-right Cayley complex code

Let $C = C[G, A, B, C_A, C_B]$. The **vertex tester** samples a uniformly random vertex $g \in G$, reads the $\Delta^2$ symbols $f_g$ of the squares containing $g$, and accepts iff $f_g \in C_A \otimes C_B$. It has locality $q = \Delta^2$, accepts every codeword with probability $1$, and its rejection probability on a word $f$ equals the fraction of vertices whose local view is not a tensor codeword.

## Proof sketch

Completeness is the definition of $C$. The locality and the formula for the rejection probability are immediate from the uniform choice of vertex.

## Depends on

- [Tensor codes on the squares of a left-right Cayley complex](square-complex-tensor-code.md)
- [Locally testable code](../locally-testable-codes/ltc.md)

## Sources

- I. Dinur, S. Evra, R. Livne, A. Lubotzky, S. Mozes, "Locally testable codes with constant rate, distance, and locality", STOC (2022), arXiv:2111.04808.
- O. Goldreich, "On the locally testable code of Dinur et al. (2021)", ECCC TR21-175 (2021).
