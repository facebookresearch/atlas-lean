# Compression schemes for thresholds and intervals

On the real line, the class of thresholds $x \mapsto 1[x < a]$ is closed under intersection and has VC dimension $1$, so it has a sample compression scheme of size $1$ (Floyd and Warmuth, Section 3: the results of Helmbold, Sloan and Warmuth "lead to compression schemes of size at most $d$ for any intersection closed class of VC dimension $d$"). The class of intervals on the line has a scheme of size $2$, keeping the positive examples with extremal values (Shalev-Shwartz and Ben-David, Section 30.2.1, axis aligned rectangles in dimension $1$; Floyd and Warmuth, Section 3, example "intervals on the line"). The thresholds on $[0,1]$ have infinite Littlestone dimension (Shalev-Shwartz and Ben-David, Example 21.4), so no deterministic online learner has a finite mistake bound for them, yet they are PAC learnable in the realizable setting through the size-$1$ scheme (Shalev-Shwartz and Ben-David, Theorem 30.2).

## Proof sketch

On a realizable sample of an interval, the smallest interval containing the two extreme positive instances contains every positive and no negative example. Infinite Littlestone dimension follows from binary search on the dyadic points of $[0,1]$; PAC learnability is the compression bound with no sample error.

Derived (not stated in the cited sources): on any linear order $X$, the class of binary concepts whose positive set is a lower set (on $\mathbb{R}$ or $\mathbb{N}$: the thresholds $x \le \theta$, $x < \theta$ and the two constants) has a scheme of size $1$: keep the positive example with the largest instance and label $x$ positive iff it lies below a kept positive instance; on a realizable sample every instance below the largest positive instance is positive and every instance above it is negative. The class of concepts whose positive set is order-connected has a scheme of size $2$, keeping the smallest and largest positive instances. On every infinite linear order the thresholds $x < \theta$ have infinite Littlestone dimension, by binary search on an infinite chain, and on a countable linear order with measurable singletons they are PAC learnable in the realizable setting through the size-$1$ scheme.

## Depends on

- [Labelled sample compression scheme](labelled-sample-compression-scheme.md)
- [The Littlestone dimension is the optimal mistake bound](../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [Littlestone-Warmuth compression bound in the realizable setting](realizable-compression-bound.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014, Example 21.4, Theorem 30.2 and Section 30.2.1.
- S. Floyd and M. K. Warmuth, "Sample Compression, Learnability, and the Vapnik-Chervonenkis Dimension", Machine Learning, 1995; technical report version UCSC-CRL-93-13, University of California, Santa Cruz, 1993, Section 3: <https://tr.soe.ucsc.edu/sites/default/files/technical-reports/UCSC-CRL-93-13.pdf>.
