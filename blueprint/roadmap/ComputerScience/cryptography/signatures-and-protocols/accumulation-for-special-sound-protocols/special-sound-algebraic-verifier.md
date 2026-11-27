# Special-sound protocols with algebraic degree-d verifiers

A $(2k-1)$-move public-coin interactive proof for a relation $\mathcal{R}$, in which the prover sends $m_1,\dots,m_k$ and the verifier sends random challenges $r_1,\dots,r_{k-1}\in\mathbb{F}$, is *$(a_1,\dots,a_{k-1})$-out-of-$|\mathbb{F}|$ special sound* if a witness can be computed efficiently from any tree of accepting transcripts with $a_i$ distinct challenges at each level $i$. Its verifier is *algebraic of degree $d$* if it accepts iff $V(x,m_1,\dots,m_k,r_1,\dots,r_{k-1})=\mathbf{0}\in\mathbb{F}^{\ell}$ for a polynomial map $V$ of total degree at most $d$. Writing $V=\sum_{j=0}^{d}V_j$ with $V_j$ homogeneous of degree $j$, the *relaxed verifier* with slack $\mu\in\mathbb{F}$ and error $\mathbf{e}\in\mathbb{F}^{\ell}$ checks $\sum_{j=0}^{d}\mu^{d-j}V_j(\cdot)=\mathbf{e}$; honest transcripts satisfy it with $\mu=1$, $\mathbf{e}=\mathbf{0}$.

## Depends on

- [Interactive arguments](../zero-knowledge-and-arguments/interactive-arguments.md)
- [Zero-knowledge interactive proofs](../zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)

## Sources

- Benedikt Bünz, Binyi Chen, "Protostar: Generic Efficient Accumulation/Folding for Special-Sound Protocols", ASIACRYPT (2023), IACR ePrint 2023/620.
