# Run of a query algorithm

A $T$-query algorithm is given by linear isometries $U_0, U_1, \dots, U_T$ of a complex inner product
space and an initial state $\psi_0$. Run with an oracle map $R$, its state after the $k$-th step is

$$\psi_0' = U_0\psi_0, \qquad \psi_{k+1}' = U_{k+1} R\, \psi_k',$$

and its final state is $\psi_T'$. The steps $U_k$ do not depend on the oracle (Bennett, Bernstein,
Brassard and Vazirani, Section 3.1). Using isometries rather than unitaries makes the results below
apply to a slightly larger class of algorithms.

## Sources

- C. H. Bennett, E. Bernstein, G. Brassard and U. Vazirani, "Strengths and weaknesses of quantum computing", SIAM Journal on Computing 26 (1997), 1510–1523; arXiv:quant-ph/9701001, Section 3.1 (Definition 3.2, Theorem 3.3, Corollary 3.4, Theorem 3.5).
- E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on Computing 26 (1997), 1411–1473; author-hosted version dated September 8, 1997, Theorem 3.4.1 (theorem number as in that version).
