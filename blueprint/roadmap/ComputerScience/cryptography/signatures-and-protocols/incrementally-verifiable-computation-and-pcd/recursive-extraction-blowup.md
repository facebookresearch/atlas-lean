# Size bound for recursively composed knowledge extractors

Suppose a proof system's knowledge extractor $\mathsf{E}$ for a prover of size $t$ has size at most $c\cdot t^{k}$ for constants $c\ge 1$, $k\ge 1$. In recursive composition, where the statement at depth $j$ asserts the existence of an accepting proof at depth $j-1$, extracting a full transcript of depth $d$ applies $\mathsf{E}$ to provers that are themselves extractors, and the size of the depth-$d$ extractor is at most $c^{(k^{d}-1)/(k-1)}\,t^{k^{d}}$ for $k>1$, and at most $c^{d}\,t$ for $k=1$. This upper bound is polynomial in $t$ when $d=O(1)$, and for $k=1$ also when $c^{d}$ is polynomial, for example $d=O(\log t)$ with $c$ constant. It is a guarantee for those depths, not a lower bound: it does not show that extraction fails at larger depths, only that this argument gives no polynomial bound there. This is why knowledge-sound PCD from extractable SNARKs is proven for constant-depth compliance predicates, and IVC for polynomially many steps is obtained via trees of constant depth.

## Proof sketch

Let $T_j$ bound the size of the depth-$j$ extractor; then $T_0=t$ and $T_j\le c\,T_{j-1}^{k}$. Unrolling the recurrence gives $T_d\le c^{1+k+\dots+k^{d-1}}t^{k^{d}}$, which is the stated bound. For $k=1$ the exponent of $t$ stays $1$ and the constant multiplies to $c^{d}$.

## Depends on

- [Proof-carrying data for a compliance predicate](pcd-scheme.md)
- [Knowledge soundness](../zero-knowledge-and-arguments/knowledge-soundness.md)
- [Incrementally verifiable computation scheme for an iterated function](ivc-scheme.md)

## Sources

- Nir Bitansky, Ran Canetti, Alessandro Chiesa, Eran Tromer, "Recursive Composition and Bootstrapping for SNARKs and Proof-Carrying Data", STOC (2013), Section 2.2 and Remark 6.3.
- Paul Valiant, "Incrementally Verifiable Computation or Proofs of Knowledge Imply Time/Space Efficiency", TCC (2008).
