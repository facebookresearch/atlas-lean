# Compression schemes for thresholds and intervals

On a linear order $X$, the class of binary concepts whose positive set is a lower set (on $\mathbb{R}$ or $\mathbb{N}$: the thresholds $x \le \theta$, $x < \theta$ and the two constants) has a sample compression scheme of size $1$: keep the positive example with the largest instance and label $x$ positive iff it lies below a kept positive instance. The class of concepts whose positive set is order-connected (on $\mathbb{R}$ or $\mathbb{N}$: all intervals) has a scheme of size $2$, keeping the smallest and largest positive instances. On an infinite linear order the thresholds $x < \theta$ have infinite Littlestone dimension, so no deterministic online learner has a finite mistake bound for them, yet on a countable linear order with measurable singletons they are PAC learnable in the realizable setting through the size-$1$ scheme.

## Proof sketch

On a realizable sample of a lower-set concept every instance below the largest positive instance is positive and every instance above it is negative, so the reconstruction is correct on the sample; the interval case keeps both extreme positives. Infinite Littlestone dimension follows from binary search on an infinite chain; PAC learnability is the realizable compression bound.

## Depends on

- [Labelled sample compression scheme](labelled-sample-compression-scheme.md)
- [The Littlestone dimension is the optimal mistake bound](../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [Littlestone-Warmuth compression bound in the realizable setting](realizable-compression-bound.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
- S. Floyd and M. K. Warmuth, "Sample Compression, Learnability, and the Vapnik-Chervonenkis Dimension", Machine Learning, 1995.
