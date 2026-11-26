# A polynomial-time statement map transfers efficient special-HVZK simulation and efficient verification

Let $(P'_i)$ be an indexed family of Sigma protocols with word encodings of index, statements, commitments, challenges and responses, and let $g_i$ be statement maps whose word form $g^w$ is computable in deterministic polynomial time and agrees with $g_i$ on encodings; let the derived family $(P'_i)_{f_i, g_i}$ use a new statement encoding. If condition (i) of a language reduction holds and $P'$ has special HVZK realized by one uniform strict probabilistic polynomial-time simulator within statistical distance $\delta_i$ of an exact special-HVZK simulator, then the derived family has the same property with the same $\delta_i$; the derived simulator computes $g$ and runs the simulator of $P'$. Likewise, if the deterministic acceptance test of $P'$ on transcripts is polynomial-time computable, so is the derived verifier's test. The witness map $f$ need not be efficient, and the efficiency of the derived honest prover is not asserted.

## Proof sketch

Compose the polynomial-time program for $g^w$ with the simulator (respectively verifier) program of $P'$; polynomial-time composition preserves strict PPT bounds, and correctness of the composition on encodings follows from agreement of $g^w$ with $g$ and the non-efficient transfer.

## Depends on

- [Derived Sigma protocols along a language reduction inherit completeness and special HVZK](sigma-protocols-along-language-reductions.md)

## Proof depends on

- [Derived Sigma protocols along a language reduction inherit completeness and special HVZK](sigma-protocols-along-language-reductions.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
