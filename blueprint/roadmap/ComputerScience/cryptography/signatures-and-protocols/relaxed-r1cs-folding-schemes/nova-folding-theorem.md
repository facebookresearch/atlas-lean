# Nova's folding scheme for committed relaxed R1CS

Consider the public-coin protocol on committed relaxed R1CS instances $U_i=(\overline{E}_i,u_i,\overline{W}_i,x_i)$: the prover sends $\overline{T}=\mathsf{Com}(pp,T,r_T)$ for the cross term $T$; the verifier sends a uniformly random $r\in\mathbb{F}$; both output $U=(\overline{E}_1+r\overline{T}+r^{2}\overline{E}_2,\;u_1+ru_2,\;\overline{W}_1+r\overline{W}_2,\;x_1+rx_2)$, and the prover outputs $W=W_1+rW_2$, $E=E_1+rT+r^{2}E_2$ with combined randomness. If the commitment scheme is additively homomorphic and computationally binding, this is a public-coin folding scheme with perfect completeness and knowledge soundness, and it is zero-knowledge when the commitment is hiding. The verifier performs three group scalar multiplications ($r\overline{T}$, $r^{2}\overline{E}_2$ and $r\overline{W}_2$) and $O(\ell)$ field operations, and two when $U_2$ is a fresh instance with $\overline{E}_2=\mathsf{Com}(pp,\mathbf{0},0)$ and $u_2=1$.

## Proof sketch

Completeness is the cross-term identity together with homomorphism of commitments. For knowledge soundness, rewind the prover to obtain three accepting transcripts with distinct challenges; interpolation recovers $W_1,W_2$ from the linear relation $W=W_1+rW_2$ and $E_1,T,E_2$ from the quadratic relation, and binding guarantees the openings match the committed values. Substituting into the folded relation at three points shows the quadratic polynomial in $r$ vanishes identically, so each input is satisfied.

## Depends on

- [Folding scheme for an NP relation](folding-scheme.md)
- [Cross-term identity for folding relaxed R1CS](nova-cross-term.md)
- [The binding experiment](../commitment-schemes/the-computational-binding-game-for-keyed-commitm/binding-game.md)
- [Relaxed R1CS instances with slack vector and scalar](relaxed-r1cs.md)

## Proof depends on

- [Pedersen commitment scheme](../commitment-schemes/pedersen-commitments-perfect-hiding-and-binding/scheme.md)
- [Interpolation extractor from three folding transcripts](three-transcript-extraction.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla, "Nova: Recursive Zero-Knowledge Arguments from Folding Schemes", CRYPTO (2022), IACR ePrint 2021/370.
