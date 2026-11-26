# Micali's computationally sound proofs

Let $V$ be a PCP verifier and let $h$ (for the Merkle tree) and $H$ (for Fiat–Shamir) be random oracles. *Micali's construction* compiles Kilian's protocol into a non-interactive argument: the prover commits to the PCP table $\pi$ by its Merkle root $\mathrm{rt}$ under $h$, derives the PCP randomness for $k$ repetitions as $\rho = H(x, \mathrm{rt})$ (possibly with a counter), and outputs $\mathrm{rt}$ together with the queried entries of $\pi$ and their authentication paths. The verifier recomputes $\rho$, checks every path against $\mathrm{rt}$ and runs $V$ on the opened entries.

## Depends on

- [Succinct arguments from probabilistically checkable proofs](../succinct-arguments-from-probabilistically.md)
- [The random oracle model](../../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [Merkle root](../../../hash-functions/merkle-trees/root.md)
- [Probabilistically checkable proofs](../../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pcp.md)

## Sources

- Silvio Micali, "Computationally Sound Proofs", SIAM Journal on Computing, 2000.
- Alessandro Chiesa and Eylon Yogev, "Building Cryptographic Proofs from Hash Functions", 2024.
