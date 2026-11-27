# Derived Sigma protocols along a language reduction inherit completeness and special HVZK

Let $R \subseteq \mathcal{X} \times \mathcal{Y}$ and $R' \subseteq \mathcal{X}' \times \mathcal{Y}'$ be relations, $f : \mathcal{X} \times \mathcal{Y} \to \mathcal{X}'$ a witness map and $g : \mathcal{Y} \to \mathcal{Y}'$ a statement map. A *language reduction* requires (i) $(x, y) \in R \Rightarrow (f(x, y), g(y)) \in R'$ and (ii) if $g(y)$ has a witness in $R'$ then $y$ has a witness in $R$. Given a Sigma protocol $P'$ for $R'$, the derived protocol $P'_{f,g}$ runs the prover of $P'$ on $(f(x,y), g(y))$ and the verifier of $P'$ on $g(y)$, keeping commitments, challenges and responses. Under condition (i) alone, completeness and special honest-verifier zero knowledge of $P'$ transfer to $P'_{f,g}$ (the simulator computes $g$ and runs that of $P'$). Special soundness transfers to the relation "$w$ is a witness of $g(y)$", and maps back to $R$ when a witness map back is given.

## Proof sketch

Transcripts of $P'_{f,g}$ on $(x, y)$ are transcripts of $P'$ on $(f(x,y), g(y))$, which lies in $R'$ by (i), so completeness and the simulated transcript law are inherited; the verifier only sees $g(y)$. An extractor for $P'$ on $g(y)$ outputs a witness for $g(y)$.

## Depends on

- [A Sigma protocol](../zero-knowledge-proofs/sigma-protocol.md)
- [Completeness of a Sigma protocol](../zero-knowledge-proofs/complete.md)
- [Perfect special honest-verifier zero knowledge](../zero-knowledge-proofs/special-hvzk.md)
- [Special soundness of a Sigma protocol](../zero-knowledge-proofs/special-sound.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
