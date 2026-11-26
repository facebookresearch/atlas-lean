# Soundness and straight-line knowledge soundness of the BCS transform

Let an IOP be complete and round-by-round sound with round errors $\varepsilon_i$ and query-phase error $\varepsilon_{\mathrm{query}}$ (and round-by-round knowledge sound with a straight-line extractor of the oracle tables). Then the BCS transform with digest length $\sigma$ is perfectly complete, and for every prover making at most $t_{MT}$ Merkle-oracle queries and $t_{FS}$ Fiat–Shamir queries, the probability of producing an accepted proof of a false statement is at most

$$
t_{FS} \cdot \max\bigl(\max_i \varepsilon_i,\ \varepsilon_{\mathrm{query}}\bigr) + O\!\left(\frac{t_{MT}^2}{2^{\sigma}}\right),
$$

where the last term bounds Merkle collisions and inversions (out-of-order Fiat–Shamir targets and forbidden digests). Moreover there is a straight-line extractor, which only reads the recorded query–answer trace, that reconstructs all IOP oracle tables (and hence a witness) from any accepted proof, except with probability bounded by the same expression: on a collision-free trace recording all opened paths, the reconstructed tables are accepted by the IOP verifier whenever the proof is accepted by the BCS verifier, and otherwise a Merkle collision is extracted. The verifier makes exactly $k$ Fiat–Shamir queries and a number of Merkle queries equal to the total length of the opened paths.

## Proof sketch

Maintain a good-state invariant on the two oracle traces: the Merkle trace is collision free and every recorded Fiat–Shamir chain corresponds to a doomed IOP prefix. A single oracle call breaks the invariant with probability at most the round escape error (Fiat–Shamir call) or a birthday-type term (Merkle call); sum over calls. On a good final state the opened paths determine unique tables, whose IOP transcript is doomed, so the verifier rejects.

## Depends on

- [The BCS transform](bcs-transform.md)

## Proof depends on

- [Prefix union bound for round-by-round sound IOPs](iop-prefix-union-bound.md)
- [Existential soundness of Merkle inclusion proofs](../../../hash-functions/merkle-trees/verify-sound.md)

## Sources

- Eli Ben-Sasson, Alessandro Chiesa and Nicholas Spooner, "Interactive Oracle Proofs", Theory of Cryptography – TCC 2016-B, Part II, 2016.
- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024.
