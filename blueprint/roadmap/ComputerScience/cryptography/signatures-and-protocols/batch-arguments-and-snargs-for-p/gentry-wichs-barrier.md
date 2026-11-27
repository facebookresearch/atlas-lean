# No black-box reduction proves adaptive SNARGs for NP sound from falsifiable assumptions

Assume there is a sub-exponentially hard subset-membership problem in NP: an efficiently samplable distribution over statements of an NP language together with witnesses, and a distribution over non-statements, that no algorithm of size $2^{\Omega(n^{\delta})}$ distinguishes with advantage more than $2^{-\Omega(n^{\delta})}$, for some constant $\delta>0$ and security parameter $n$ (for instance, the output distribution of a sub-exponentially secure pseudorandom generator versus uniform strings outside its range). Then no succinct non-interactive argument for an NP-complete language, with proof size $\mathrm{poly}(\lambda)\cdot(|x|+|w|)^{o(1)}$, can have its adaptive soundness proven by a black-box reduction to a falsifiable assumption, unless the assumption is false. If an NP language $L$ has an exponentially hard subset-membership problem, the same holds for slightly succinct arguments for $L$, with proof size $\mathrm{poly}(\lambda)\cdot(|x|+|w|)^{c}+o(|x|+|w|)$ for a constant $c<1$ (Theorem 5.1); the extension to every NP-complete language (Corollary 5.2) requires full succinctness. This explains why SNARGs from standard assumptions are obtained either for restricted languages (deterministic computations), with non-adaptive soundness, or relative to non-falsifiable assumptions.

## Proof sketch

Construct a simulatable adversary that outputs false statements with accepting-looking proofs indistinguishable, to any efficient observer, from true statements with honest proofs, using the assumed hard problems; a black-box reduction cannot tell whether it interacts with this inefficiently-sound adversary, so it would break the falsifiable assumption using an efficient simulator.

## Depends on

- [Succinct arguments and SNARKs](../zero-knowledge-and-arguments/succinct-arguments-and-snarks.md)

## Sources

- Craig Gentry, Daniel Wichs, "Separating Succinct Non-Interactive Arguments from All Falsifiable Assumptions", STOC (2011), IACR ePrint 2010/610, Definition 2.5, Theorem 5.1 and Corollary 5.2.
