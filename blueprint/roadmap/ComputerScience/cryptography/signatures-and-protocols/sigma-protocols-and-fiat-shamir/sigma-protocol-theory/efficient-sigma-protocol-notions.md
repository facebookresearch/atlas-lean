# Efficient special soundness, efficient special HVZK and computational special HVZK

Let $\Pi$ be a Sigma protocol for a relation $\mathcal{R}$ (statements $y$, witnesses $x$) with challenge set $C$. *Efficient special soundness* requires a deterministic polynomial-time extractor that, from two accepting conversations $(t, c, z)$, $(t, c', z')$ with $c \ne c'$, outputs a witness for $y$. *Efficient special honest-verifier zero knowledge* requires a probabilistic polynomial-time simulator that, given $y$ and $c$, outputs $(t, z)$ distributed as the honest conversation with challenge $c$ (exactly, or within statistical distance $\delta$). For an indexed family of protocols with a setup sampler, *computational special HVZK* requires that no efficient distinguisher, choosing $(x, y) \in \mathcal{R}$ and $c$, tells the honest conversation from the simulated one with non-negligible advantage. Efficient statistical special HVZK with negligible realization error implies computational special HVZK. *Unique responses* means that two accepting conversations $(t, c, z)$ and $(t, c, z')$ have $z = z'$, and *strong special soundness* means extraction succeeds from accepting $(t, c, z)$, $(t, c', z')$ whenever $(c, z) \ne (c', z')$.

## Depends on

- [A Sigma protocol](../../zero-knowledge-proofs/sigma-protocol.md)
- [Special soundness of a Sigma protocol](../../zero-knowledge-proofs/special-sound.md)
- [Perfect special honest-verifier zero knowledge](../../zero-knowledge-proofs/special-hvzk.md)
- [Probabilistic polynomial-time Turing machines](../../../security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
