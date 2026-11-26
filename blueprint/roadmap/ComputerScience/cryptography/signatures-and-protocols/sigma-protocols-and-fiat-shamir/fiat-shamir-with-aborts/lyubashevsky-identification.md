# Lyubashevsky's lattice identification protocol

Let $q$, $n$, $m$, $k$ be positive integers and $0 < \beta \le \gamma$. The statement is $(A, T)$ with $A \in \mathbb{Z}_q^{n \times m}$ and $T \in \mathbb{Z}_q^{n \times k}$, and a witness is an integer matrix $S \in \mathbb{Z}^{m \times k}$ with $A S \equiv T$ and $\|S\|_\infty \le \eta$. The prover draws a mask $y$ uniformly from the box $[-\gamma, \gamma]^m$ and sends $t = A y$; on challenge $c \in \{0,1\}^k$ it computes $z = y + S c$ and sends $z$ if $\|z\|_\infty \le \gamma - \beta$, and aborts otherwise (rejection sampling). The verifier accepts $z$ if $\|z\|_\infty \le \gamma - \beta$ and $A z \equiv t + T c$.

## Depends on

- [Sigma protocols with aborts](sigma-protocols-with-aborts.md)
- [The short integer solution problem (SIS)](../../../public-key/lattice-and-code-based-cryptography/lattice-problems/short-integer-solution-problem.md)

## Sources

- Vadim Lyubashevsky, "Fiat-Shamir with Aborts: Applications to Lattice and Factoring-Based Signatures", Advances in Cryptology – ASIACRYPT 2009, 2009.
- Vadim Lyubashevsky, "Lattice Signatures without Trapdoors", Advances in Cryptology – EUROCRYPT 2012, 2012.
- Léo Ducas et al., "CRYSTALS-Dilithium: A Lattice-Based Digital Signature Scheme", IACR Transactions on Cryptographic Hardware and Embedded Systems, 2018.
