# Universal learning rates trichotomy

This node collects the universal learning rates of Bousquet, Hanneke, Moran, van Handel and Yehudayoff in the
realizable setting.

## Expansion

A sound expansion has separate pages for:

1. **Universal rates.** A class has universal rate $R(n)$ if some learner achieves expected error at most
   $C R(c n)$ for every realizable distribution, with constants depending on the distribution, and no learner does
   better than $R$ in the same sense; measurability assumptions on the class are those of the source.
2. **Trichotomy.** For every concept class with at least three functions, the optimal universal rate is
   exponential, linear, or arbitrarily slow: exponential if the class has no infinite Littlestone tree, linear if
   it has one but no infinite VCL tree, and arbitrarily slow otherwise.
3. **Degenerate classes.** Classes with one or two functions, whose error can be zero after finitely many samples,
   are handled by the source's conventions and are not counterexamples to the trichotomy.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Shattering and VC dimension.

## Depends on

- [The Littlestone dimension is the optimal mistake bound](../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Sources

- A Theory of Universal Learning (Bousquet, Hanneke, Moran, van Handel, Yehudayoff; STOC 2021; arXiv:2011.04483) — arXiv / STOC 2021: Theorem 1.6 (trichotomy for classes with at least three functions) and its characterization by infinite Littlestone and VCL trees. <https://arxiv.org/abs/2011.04483>
