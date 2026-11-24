# Homomorphic encryption: correctness and compactness

A public-key homomorphic encryption scheme for a class $\mathcal{C}$ of circuits adds to key generation, encryption and decryption an algorithm $\mathrm{Eval}(pk, C, c_1, \dots, c_k)$. It is *correct* for $\mathcal{C}$ if for every $C \in \mathcal{C}$ with $k$ inputs, all messages $m_1, \dots, m_k$ and all ciphertexts $c_i$ output by $\mathrm{Enc}(pk, m_i)$, $\mathrm{Dec}(sk, \mathrm{Eval}(pk, C, c_1, \dots, c_k)) = C(m_1, \dots, m_k)$. It is *compact* if there is a polynomial $f$ such that, for every security parameter $\lambda$, decryption of the outputs of $\mathrm{Eval}$ is computed by a circuit of size at most $f(\lambda)$, independently of the evaluated circuit $C$. A *leveled* fully homomorphic scheme takes a depth bound $L$ as an input to key generation and is correct and compact for all circuits of depth at most $L$, with one decryption circuit for all of them, whose size may depend polynomially on $L$; a *fully homomorphic* scheme is correct and compact for all circuits.

## Depends on

- [Public-key encryption scheme](../../security-games/generic-security-games/pkescheme.md)

## Expansion

This page becomes ready once:

- Schemes with negligible decryption failure need the overwhelming-probability variant of correctness, stated separately

## Sources

- C. Gentry, "Fully homomorphic encryption using ideal lattices", *Proceedings of the 41st ACM STOC*, 2009
- Z. Brakerski, C. Gentry and V. Vaikuntanathan, "(Leveled) fully homomorphic encryption without bootstrapping", *ITCS 2012*, ACM, 2012
