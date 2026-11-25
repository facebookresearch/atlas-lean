# AND and OR composition of Sigma protocols

Let $(P_0, V_0)$ and $(P_1, V_1)$ be Sigma protocols for relations $R_0 \subseteq Y_0 \times X_0$ and $R_1 \subseteq Y_1 \times X_1$ between statements $y$ and witnesses $x$, written in the order (statement, witness), with the same challenge space $C$.

- *AND.* For $R_{\mathrm{AND}} = \{((y_0, y_1), (x_0, x_1)) : (y_0, x_0) \in R_0 \text{ and } (y_1, x_1) \in R_1\}$, the prover sends the commitments $(t_0, t_1)$ of both protocols, the verifier sends one challenge $c \in C$, the prover answers it in both protocols with $(z_0, z_1)$, and the verifier accepts if $(t_0, c, z_0)$ and $(t_1, c, z_1)$ are accepting conversations for $y_0$ and $y_1$. This is a Sigma protocol for $R_{\mathrm{AND}}$; it provides knowledge soundness if both protocols do, and it is special honest-verifier zero knowledge if both are.
- *OR.* Suppose moreover that $C = \{0,1\}^n$ and that both protocols are special honest-verifier zero knowledge with simulators $\mathrm{Sim}_0$, $\mathrm{Sim}_1$. For $R_{\mathrm{OR}} = \{((y_0, y_1), (b, x)) : (y_b, x) \in R_b\}$, a prover with witness $(b, x)$ and $d = 1 - b$ picks a uniformly random $c_d \in C$, computes $(t_d, z_d) = \mathrm{Sim}_d(y_d, c_d)$, runs $P_b(x, y_b)$ for a commitment $t_b$ and sends $(t_0, t_1)$; on the verifier's random challenge $c$ it answers $c_b = c \oplus c_d$ in $P_b$, obtaining $z_b$, and sends $(c_0, z_0, z_1)$; the verifier sets $c_1 = c \oplus c_0$ and accepts if $(t_0, c_0, z_0)$ and $(t_1, c_1, z_1)$ are accepting conversations for $y_0$ and $y_1$. This is a special honest-verifier zero-knowledge Sigma protocol for $R_{\mathrm{OR}}$, and it provides knowledge soundness if both protocols do.
- *Witness independence.* Every special honest-verifier zero-knowledge Sigma protocol is witness independent; in particular the OR protocol is.

## Expansion

This page collects several results; it becomes ready once each is stated separately:

- AND composition of Sigma protocols, as a page of its own
- OR composition of Sigma protocols, as a page of its own

## Depends on

- [A Sigma protocol](../zero-knowledge-proofs/sigma-protocol.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Sections 19.7.1 and 19.7.2, Theorems 19.17 and 19.18, and Section 19.8.2, Theorem 19.20
- Original construction: R. Cramer, I. Damgård and B. Schoenmakers, "Proofs of partial knowledge and simplified design of witness hiding protocols", *CRYPTO 1994*, LNCS 839, Springer, 1994.
