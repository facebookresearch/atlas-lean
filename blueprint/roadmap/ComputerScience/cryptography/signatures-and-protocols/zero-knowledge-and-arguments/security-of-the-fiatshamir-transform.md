# Security of the Fiat–Shamir transform

Let $\Pi$ be a Sigma protocol for a relation $R$ with challenge space $C$, and let $H$ be modelled as a random oracle onto $C$. In the Fiat–Shamir non-interactive proof, the prover computes its commitment $t$, sets the challenge $c = H(y, t)$ and outputs $(t, z)$. A Sigma protocol is *existentially sound* if no efficient adversary that chooses a statement $y$ and then plays the prover against the verifier $V(y)$ makes it accept with non-negligible probability while $y \notin L_R$; a non-interactive proof system is existentially sound if no efficient adversary outputs a statement $y \notin L_R$ and an accepted proof except with negligible probability. If $\Pi$ is existentially sound, the non-interactive proof is existentially sound: for every adversary $A$ making at most $Q_{\mathrm{ro}}$ random-oracle queries there is an adversary $B$ against the existential soundness of $\Pi$ with

$$\mathrm{Adv}^{\mathrm{niES}}[A, \text{FS-}\Pi] \le (Q_{\mathrm{ro}} + 1)\cdot \mathrm{Adv}^{\mathrm{ES}}[B, \Pi].$$

If $\Pi$ is special honest-verifier zero knowledge and has $\kappa$-unpredictable commitments, the non-interactive proof is zero knowledge: there is a simulator, programming the random oracle, such that every adversary making at most $Q_p$ justified proof queries and $Q_{\mathrm{ro}}$ random-oracle queries has advantage at most $Q_p(Q_p + Q_{\mathrm{ro}})\cdot\kappa$.

## Depends on

- [A Sigma protocol](../zero-knowledge-proofs/sigma-protocol.md)
- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Section 20.3, Attack Games 20.1 and 20.2, Definitions 20.2 and 20.4, Theorems 20.2 and 20.3
- Original transform: A. Fiat and A. Shamir, "How to prove yourself: practical solutions to identification and signature problems", *CRYPTO 1986*, LNCS 263, Springer, 1987.
