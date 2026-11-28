# Completeness and soundness of Micali's construction in the random oracle model

Micali's construction is perfectly complete: if $V$ accepts the table $(x, \pi)$, then for every digest length $\sigma$ and every number of repetitions the honest proof is accepted with probability $1$. It is sound in the random oracle model: for every statement $x \notin L$ and every prover making at most $t$ queries to the two oracles, the probability of producing an accepted proof is at most

$$
(t + 1) \cdot \varepsilon_{\mathrm{PCP}}^{\,k} + \frac{3}{2}\frac{(t - 1)t}{2^{\sigma}} + \frac{(d + 1)\cdot 2\ell}{2^{\sigma}} + \frac{t^2}{2^{\sigma}},
$$

where $\ell$ is the PCP table length and $d = \lceil \log_2 \ell \rceil$ is the depth of the Merkle tree (matching Chiesa and Yogev, Theorem 21.2.1 and Lemma 18.5.7, whose Merkle term $\kappa^{\mathrm{m}}_{\mathrm{MT}}(\sigma, \ell, t, t + 1)$ is at most $\frac{2.5\, t^2}{2^{\sigma}}$ for $t \ge 2(\log_2 \ell + 1)\ell$): either the query trace contains a collision or an inversion of the Merkle oracle, or the proof's root is consistent with one PCP table and each of the at most $t$ Fiat–Shamir queries of the prover, and the verifier's own Fiat–Shamir query, yields PCP randomness accepting that table with probability at most $\varepsilon_{\mathrm{PCP}}^k$. The verifier runs in time polynomial in $|x|$ and $\sigma$ and makes a number of oracle queries polylogarithmic in the table length, even on arbitrary (unframed or oversized) proof strings.

## Proof sketch

Fix the oracle trace: if it is collision-free and records all hash steps of the openings, then the root determines a unique table along the opened paths, and acceptance reduces to the PCP verifier accepting that table on the Fiat–Shamir randomness; a union bound over the prover's Fiat–Shamir queries and the verifier's own query bounds the latter, and collisions in the Merkle oracle are bounded by the birthday bound.

## Depends on

- [Micali's computationally sound proofs](micali-cs-proofs.md)

## Proof depends on

- [Soundness of Kilian's protocol from Merkle position binding](kilian-exact-soundness.md)
- [Existential soundness of Merkle inclusion proofs](../../../hash-functions/merkle-trees/verify-sound.md)

## Sources

- Silvio Micali, "Computationally Sound Proofs", SIAM Journal on Computing, 2000.
- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024, Theorem 21.2.1 and Lemma 18.5.7.
