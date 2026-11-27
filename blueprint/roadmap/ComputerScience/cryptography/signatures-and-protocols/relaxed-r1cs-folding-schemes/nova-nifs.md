# Non-interactive folding via Fiat–Shamir in the random oracle model

Replacing the verifier's challenge $r$ in Nova's folding protocol by $r=\rho(\mathsf{vk},U_1,U_2,\overline{T})$ for a random oracle $\rho$ yields a *non-interactive folding scheme (NIFS)* that remains knowledge sound in the random oracle model. Since the protocol has a single challenge and is special sound with three transcripts, the extractor uses forking on the random oracle query and loses at most a polynomial factor in the adversary's query bound $Q$ and an additive term $O(Q/|\mathbb{F}|)$ in success probability.

## Proof sketch

Apply the forking lemma to the query defining $r$: run the adversary, then rerun it with fresh oracle answers from that query on, until three accepting outputs with distinct challenges are obtained; the expected number of reruns is polynomial in $Q$ and the inverse success probability. The interpolation extractor then recovers the witnesses.

## Depends on

- [Nova's folding scheme for committed relaxed R1CS](nova-folding-theorem.md)
- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)
- [Folding scheme for an NP relation](folding-scheme.md)

## Proof depends on

- [Security of the Fiat–Shamir transform](../zero-knowledge-and-arguments/security-of-the-fiatshamir-transform.md)
- [Interpolation extractor from three folding transcripts](three-transcript-extraction.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla, "Nova: Recursive Zero-Knowledge Arguments from Folding Schemes", CRYPTO (2022), IACR ePrint 2021/370.
