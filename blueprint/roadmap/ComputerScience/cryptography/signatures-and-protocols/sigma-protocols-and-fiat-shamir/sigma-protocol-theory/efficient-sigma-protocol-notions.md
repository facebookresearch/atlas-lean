# Efficient special soundness, efficient special HVZK and computational special HVZK

Let $\Pi$ be a Sigma protocol for a relation $\mathcal{R}$ (statements $y$, witnesses $x$) with challenge set $C$. *Efficient special soundness* requires a polynomial-time extractor that, from two accepting conversations $(t, c, z)$, $(t, c', z')$ with $c \ne c'$, outputs a witness for $y$. *Efficient special honest-verifier zero knowledge* requires a probabilistic polynomial-time simulator that, given $y$ and $c$, outputs $(t, z)$ distributed as the honest conversation with challenge $c$ (exactly, or within statistical distance $\delta$). For an indexed family of protocols, *computational special HVZK* requires instead that, for every $(x, y) \in \mathcal{R}$ and every $c$, the honest conversation with challenge $c$ and the simulated one are computationally indistinguishable. Efficient statistical special HVZK with negligible realization error implies computational special HVZK. *Unique responses* means that two accepting conversations $(t, c, z)$ and $(t, c, z')$ have $z = z'$, and *strong special soundness* means extraction succeeds from accepting $(t, c, z)$, $(t, c', z')$ whenever $(c, z) \ne (c', z')$.

## Depends on

- [A Sigma protocol](../../zero-knowledge-proofs/sigma-protocol.md)
- [Special soundness of a Sigma protocol](../../zero-knowledge-proofs/special-sound.md)
- [Perfect special honest-verifier zero knowledge](../../zero-knowledge-proofs/special-hvzk.md)
- [Probabilistic polynomial-time Turing machines](../../../security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)

## Sources

- Ronald Cramer, Ivan Damgård and Berry Schoenmakers, "Proofs of Partial Knowledge and Simplified Design of Witness Hiding Protocols", Advances in Cryptology – CRYPTO '94, LNCS 839, Springer, 1994, pp. 174–187, Section 2.
- Marc Fischlin, "Communication-Efficient Non-Interactive Proofs of Knowledge with Online Extractors", Advances in Cryptology – CRYPTO 2005, LNCS 3621, Springer, 2005, pp. 152–168.
- Yashvanth Kondi and abhi shelat, "Improved Straight-Line Extraction in the Random Oracle Model with Applications to Signature Aggregation", Advances in Cryptology – ASIACRYPT 2022, Springer, 2022, Section 6.2.
