# No black-box reduction proves adaptive SNARGs for NP sound from falsifiable assumptions

Assume sub-exponentially hard one-way functions (or exponentially hard subset-membership problems). Then for no succinct non-interactive argument for NP with proof size $\mathrm{poly}(\lambda)\cdot(|x|+|w|)^{o(1)}$ can adaptive soundness be proven by a black-box reduction to any falsifiable assumption, unless the assumption is false. This explains why SNARGs from standard assumptions are obtained either for restricted languages (deterministic computations), with non-adaptive soundness, or relative to non-falsifiable assumptions.

## Proof sketch

Construct a simulatable adversary that outputs false statements with accepting-looking proofs indistinguishable, to any efficient observer, from true statements with honest proofs, using the assumed hard problems; a black-box reduction cannot tell whether it interacts with this inefficiently-sound adversary, so it would break the falsifiable assumption using an efficient simulator.

## Depends on

- [Succinct arguments and SNARKs](../zero-knowledge-and-arguments/succinct-arguments-and-snarks.md)
- [One-way functions exist](../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/impagliazzo-s-five-worlds/owfexists.md)

## Sources

- Craig Gentry, Daniel Wichs, "Separating Succinct Non-Interactive Arguments from All Falsifiable Assumptions", STOC (2011).
