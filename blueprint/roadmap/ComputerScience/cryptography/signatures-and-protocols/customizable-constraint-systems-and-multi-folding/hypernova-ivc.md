# HyperNova: IVC for high-degree constraint systems

Using the multi-folding scheme for CCS in an augmented step circuit (as in Nova, with the verifier made non-interactive in the random oracle model), one obtains an IVC scheme for any step function expressed as CCS of degree $d$, knowledge sound in the random oracle model (with the usual heuristic in-circuit hash instantiation). The prover's cryptographic work per step is one multi-scalar multiplication of size equal to the number of witness variables, independent of $d$, and the recursion overhead consists of one group scalar multiplication plus a logarithmic number of hash and field operations; because the folded relation is linear, multiple instances can be folded at once, yielding PCD.

## Proof sketch

Mirror the Nova construction with LCCCS as the running relation and CCCS as the fresh relation. Each step's circuit runs the non-interactive multi-folding verifier, whose cost is dominated by checking a degree-$(d+1)$ sum-check of $\log m$ rounds and one scalar multiplication. Knowledge soundness follows inductively by multi-folding extraction.

## Depends on

- [Incrementally verifiable computation scheme for an iterated function](../incrementally-verifiable-computation-and-pcd/ivc-scheme.md)
- [Customizable constraint systems](customizable-constraint-system.md)
- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)

## Proof depends on

- [HyperNova multi-folding scheme for CCS](hypernova-multifolding.md)
- [Nova: IVC with constant recursion overhead from folding](../relaxed-r1cs-folding-schemes/nova-ivc.md)
- [Non-interactive folding via Fiat–Shamir in the random oracle model](../relaxed-r1cs-folding-schemes/nova-nifs.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, "HyperNova: Recursive Arguments for Customizable Constraint Systems", CRYPTO (2024), IACR ePrint 2023/573.
