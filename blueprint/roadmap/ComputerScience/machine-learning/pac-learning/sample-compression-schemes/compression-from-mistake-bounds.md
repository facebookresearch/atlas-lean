# Sample compression schemes from mistake bounds and Littlestone dimension

Let $A$ be a deterministic online learner that makes at most $M$ mistakes on every sequence labelled by a concept of $C$ (labels in any set with decidable equality). Then $C$ has a sample compression scheme of size $M$ whose reconstruction is $A$ itself: run $A$ over the sample in index order, feeding it only the examples kept so far and keeping each example it labels wrongly, and repeat this pass $M+1$ times. If $C$ has Littlestone dimension at most $d$ over a nonempty label set, the Standard Optimal Algorithm yields a scheme of size $d$. Consequently, on countable domain and label spaces with measurable singletons, $C$ is PAC learnable in the realizable setting from every $m$ with $(m+1)^d(1-\varepsilon)^{m-d} \le \delta$.

## Proof sketch

After any number of passes the kept examples form, in order, a sequence on which $A$ errs at every step, so on a realizable sample at most $M$ examples are ever kept. Each pass that keeps a new example increases their number, so after $M+1$ passes some pass keeps nothing; in that pass $A$, fed the kept examples, labels every example correctly. The PAC statement is the realizable compression bound.

## Depends on

- [Labelled sample compression scheme](labelled-sample-compression-scheme.md)
- [The Littlestone dimension is the optimal mistake bound](../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [Littlestone-Warmuth compression bound in the realizable setting](realizable-compression-bound.md)

## Sources

- S. Floyd and M. K. Warmuth, "Sample Compression, Learnability, and the Vapnik-Chervonenkis Dimension", Machine Learning, 1995.
- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
