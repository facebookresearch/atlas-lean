# Word-RAM resamplable hash family

A *Word-RAM hash family* consists of a memory layout for its seed, an initialization program, a resampling program that uses `rand` instructions to draw a fresh seed, and an evaluation program that computes $h_\theta(u)$ from the stored seed $\theta$ and a key $u$ in registers. It is *exact* for a seed law $\nu$ if the resampling program's output seed is distributed exactly as $\nu$ and evaluation computes the mathematical hash function; its costs are the instruction counts of the three programs and the number of seed words.

## Depends on

- [The word-RAM model](../../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [Randomized state-transition specification and distributional refinement](../../../data-structure-interfaces-and-refinement/randomized-specification-and-refinement.md)

## Sources

- J. L. Carter and M. N. Wegman, "Universal Classes of Hash Functions", Journal of Computer and System Sciences 18(2), 1979.
- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
