# IVC is proof-carrying data on path-shaped transcripts

Let $F$ be a step function and define the compliance predicate $\varphi_F(z',w,z)=1$ iff $z'=F(z,w)$, together with a base-case predicate accepting source vertices labeled $z_0$. Any PCD system for $\varphi_F$ whose knowledge extractor succeeds on transcripts of polynomial depth yields an IVC scheme for $F$ with the same proof size and verification time: $\pi_{i+1}$ is the PCD proof for the message $(i+1,z_0,z_{i+1})$ produced from the single incoming message $(i,z_0,z_i)$.

## Proof sketch

A $\varphi_F$-compliant path transcript from the source labeled $z_0$ to the sink labeled $z_n$ is exactly a sequence $w_0,\dots,w_{n-1}$ with $z_{i+1}=F(z_i,w_i)$. Completeness of the PCD system gives IVC completeness step by step, and the PCD extractor applied to the final proof outputs such a transcript, which is the IVC witness sequence.

## Depends on

- [Proof-carrying data for a compliance predicate](pcd-scheme.md)
- [Incrementally verifiable computation scheme for an iterated function](ivc-scheme.md)

## Sources

- Nir Bitansky, Ran Canetti, Alessandro Chiesa, Eran Tromer, "Recursive Composition and Bootstrapping for SNARKs and Proof-Carrying Data", STOC (2013).
- Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla, "Nova: Recursive Zero-Knowledge Arguments from Folding Schemes", CRYPTO (2022), IACR ePrint 2021/370.
