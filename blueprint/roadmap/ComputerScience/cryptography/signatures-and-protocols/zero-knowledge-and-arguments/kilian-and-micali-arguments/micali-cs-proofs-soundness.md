# Completeness and soundness of Micali's construction in the random oracle model

Micali's construction is perfectly complete: if $V$ accepts the table $(x, \pi)$, then for every digest length $\sigma$ and every number of repetitions the honest proof is accepted with probability $1$. It is sound in the random oracle model: for every statement $x \notin L$ and every prover making at most $t$ queries to the two oracles, the probability of producing an accepted proof is at most

$$
t \cdot \varepsilon_{\mathrm{PCP}}^{\,k} + \frac{t^2}{2^{\sigma}} + \frac{t \cdot c}{2^\sigma},
$$

for a constant $c$ depending only on the depth of the Merkle tree: either the query trace contains a collision or an inversion of the Merkle oracle, or the proof's root is consistent with one PCP table and each of the at most $t$ Fiat–Shamir queries yields PCP randomness accepting that table with probability at most $\varepsilon_{\mathrm{PCP}}^k$. The verifier runs in time polynomial in $|x|$ and $\sigma$ and makes a number of oracle queries polylogarithmic in the table length, even on arbitrary (unframed or oversized) proof strings.

## Proof sketch

Fix the oracle trace: if it is collision-free and records all hash steps of the openings, then the root determines a unique table along the opened paths, and acceptance reduces to the PCP verifier accepting that table on the Fiat–Shamir randomness; a union bound over the Fiat–Shamir queries bounds the latter, and collisions in the Merkle oracle are bounded by the birthday bound.

## Depends on

- [Micali's computationally sound proofs](micali-cs-proofs.md)

## Proof depends on

- [Soundness of Kilian's protocol from Merkle position binding](kilian-exact-soundness.md)
- [Existential soundness of Merkle inclusion proofs](../../../hash-functions/merkle-trees/verify-sound.md)

## Sources

- Silvio Micali, "Computationally Sound Proofs", SIAM Journal on Computing, 2000.
- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024.
