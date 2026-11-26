# Differential privacy

A randomized algorithm (a *mechanism*) is differentially private when changing one individual's data changes the probability of every output event by at most a factor $e^\varepsilon$, up to an additive slack $\delta$ (Dwork, McSherry, Nissim and Smith 2006; Dwork and Roth 2014, Chapter 2). The definition applies to an arbitrary neighbouring relation on databases, with the histogram relation $\|x - y\|_1 \le 1$ of Dwork and Roth and the row (Hamming) relation as instances. Its basic properties are immunity to post-processing, graceful degradation for groups, and composition; further results are the advanced composition theorem, the Gaussian mechanism, and the link with generalization in adaptive data analysis.

## Definition

- [Differential privacy](differentially-private.md)
- [Neighbouring histograms](histogram-adj.md)
- [Neighbouring row databases](hamming-adj.md)
- [Monotonicity of the privacy parameters](mono.md)
- [Pure differential privacy as a measure inequality](differentially-private-zero-iff-le-smul.md)

## Post-processing

- [Post-processing by a measurable map](map.md)
- [Post-processing by a Markov kernel](bind.md)

## Group privacy

- [Group privacy along a chain](group.md)
- [Group privacy for histograms](group-histogram.md)
- [Group privacy along a chain, approximate case](group-sum.md)
- [Group privacy, approximate case](group-approx.md)

## Composition

- [Composition of pure differential privacy](prod.md)
- [Adaptive composition of pure differential privacy](comp-prod.md)
- [Composition of approximate differential privacy, two mechanisms](prod-approx.md)
- [Adaptive composition of approximate differential privacy, two mechanisms](comp-prod-approx.md)
- [Basic composition](differentially-private-pi.md)

## Further results

- [Advanced composition](differentially-private-pi-advanced.md)
- [The Gaussian mechanism](gaussian-mechanism-differentially-privat.md)
- [Gaussian calibration tail estimate](gaussian-calibration-tail-le.md)
- [Transfer theorem for adaptive data analysis](differentially-private-transfer.md)

## Discrete pure differential privacy

- [Replace-one adjacency](replace-one.md)
- [Replace-one adjacency is reflexive](refl.md)
- [Replace-one adjacency is symmetric](symm.md)
- [Pure differential privacy for discrete mechanisms](is-dp.md)
- [Event-level pure differential privacy](is-dpevent.md)
- [Pointwise and event-level pure differential privacy agree](is-dp-iff-is-dpevent.md)
- [Deterministic post-processing of a mechanism](post-process.md)
- [Pure differential privacy is preserved by deterministic post-processing](is-dp-post-process.md)
- [A database-independent mechanism is 0-differentially private](is-dp-const.md)

## Related topics

- [Laplace and exponential mechanisms](../laplace-and-exponential-mechanisms/README.md): the basic mechanisms that achieve pure differential privacy, built on this definition.
- [Total variation distance](../../../Probability/convergence-of-measures/total-variation-distance/README.md): for a symmetric neighbouring relation and probability measures, $(0, \delta)$-differential privacy says exactly that the output laws on neighbouring databases are at total variation distance at most $\delta$ (Dwork and Roth 2014, Section 3.5.1, statistical distance).
- [Data-processing inequality](../../../InformationTheory/information-inequalities/data-processing-inequality/README.md): the information-theoretic counterpart of post-processing; processing an output cannot make two inputs easier to distinguish.
- [Generalization bounds and concentration](../../machine-learning/generalization-bounds-and-concentration/README.md): differential privacy of an adaptive analyst gives generalization for adaptively chosen queries (Dwork, Feldman, Hardt, Pitassi, Reingold and Roth 2015), where union bounds over a fixed class do not apply.
- [Blatant non-privacy and distortion of subset-sum mechanisms](blatant-non-privacy-and-distortion-of-subset.md)
- [Dinur–Nissim reconstruction attack](dinurnissim-reconstruction-attack.md)
- [Packing lower bound for pure differential privacy](packing-lower-bound-for-pure-differential.md)
- [Rényi differential privacy of the Gaussian mechanism](renyi-differential-privacy-of-the-gaussian.md)
- [Fingerprinting codes](fingerprinting-codes.md)
