# Extractor blow-up in recursive proof composition

Suppose a proof system's knowledge extractor $\mathsf{E}$ for a prover of running time $t$ runs in time at most $c\cdot t^{k}$ for constants $c\ge 1$, $k\ge 1$. In recursive composition, where the statement at depth $j$ asserts the existence of an accepting proof at depth $j-1$, extracting a full transcript of depth $d$ requires applying $\mathsf{E}$ to provers that are themselves extractors, so the running time of the depth-$d$ extraction is bounded by $c^{(k^{d}-1)/(k-1)}\,t^{k^{d}}$ (and by $c^{d}\,t$ when $k=1$). Consequently, for $k>1$, extraction is polynomial-time only for $d=O(1)$, which is why knowledge-sound PCD from extractable SNARKs is proven for constant-depth transcripts and IVC for polynomially many steps is obtained via constant-depth trees.

## Proof sketch

Let $T_j$ be the running time of the depth-$j$ extractor; then $T_0=t$ and $T_j\le c\,T_{j-1}^{k}$. Unrolling the recursion gives $T_d\le c^{1+k+\dots+k^{d-1}}t^{k^{d}}$, which is the stated bound. For $k=1$ the exponent of $t$ stays $1$ and the constant multiplies to $c^{d}$.

## Depends on

- [Proof-carrying data for a compliance predicate](pcd-scheme.md)
- [Knowledge soundness](../zero-knowledge-and-arguments/knowledge-soundness.md)

## Proof depends on

- [Knowledge soundness](../zero-knowledge-and-arguments/knowledge-soundness.md)

## Sources

- Nir Bitansky, Ran Canetti, Alessandro Chiesa, Eran Tromer, "Recursive Composition and Bootstrapping for SNARKs and Proof-Carrying Data", STOC (2013).
- Paul Valiant, "Incrementally Verifiable Computation or Proofs of Knowledge Imply Time/Space Efficiency", TCC (2008).
