# AND, OR and parallel composition preserve efficient extraction and simulation

Let $\Pi_0, \Pi_1$ be Sigma protocols with a common finite challenge group $C$ (OR composition uses an abelian group of challenges). (i) If $\Pi_0$ and $\Pi_1$ have efficient special soundness, then so do the AND composition, the OR composition, and the $k$-fold parallel repetition $\Pi^k$ for every $k \ge 1$, with polynomial-time extractors. (ii) If $\Pi_0$ and $\Pi_1$ have efficient special HVZK with simulation errors $\delta_0, \delta_1$, then the AND composition has error at most $\delta_0 + \delta_1$, the OR composition has error at most $\delta_0 + \delta_1$ plus the challenge-sampling error, and $\Pi^k$ has error at most $k\delta$; the simulators are strict probabilistic polynomial time. In particular exact (zero-error) simulation is preserved.

## Proof sketch

The AND extractor runs both component extractors; the OR extractor finds a component whose two sub-challenges differ, which must exist because the sub-challenges sum to distinct challenges; parallel repetition extracts at a coordinate where the challenges differ. Simulators run the component simulators, for OR with one sub-challenge sampled uniformly and the other set to the difference.

## Depends on

- [Efficient special soundness, efficient special HVZK and computational special HVZK](efficient-sigma-protocol-notions.md)
- [AND and OR composition of Sigma protocols](../../zero-knowledge-and-arguments/and-and-or-composition-of-sigma-protocols.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
- Ronald Cramer, Ivan Damgaard and Berry Schoenmakers, "Proofs of Partial Knowledge and Simplified Design of Witness Hiding Protocols", Advances in Cryptology – CRYPTO '94, 1994.
