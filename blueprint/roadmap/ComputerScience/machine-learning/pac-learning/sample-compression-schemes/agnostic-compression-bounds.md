# Agnostic sample compression generalization bounds

Let $\kappa$ be a general sample compression scheme of size $k$ with measurable reconstruction, $D$ any distribution on $X \times \beta$, $m > k$ and $\delta > 0$. For a sample $S \sim D^m$ let $J$ be the set of distinct kept indices, $h_S$ the reconstructed hypothesis and $q$ its error rate on the held-out examples $S_i$, $i \notin J$. Put $c = (k\ln(m+1) + \ln(1/\delta))/(m-k)$. Each of the following holds with probability at least $1 - \delta$:

1. $|q - \mathrm{err}_D(h_S)| < \sqrt{(k\ln(m+1) + \ln(2/\delta))/(2(m-k))}$;
2. $\mathrm{err}_D(h_S) \le q + c + \sqrt{c^2 + 2qc}$, and hence $\mathrm{err}_D(h_S) \le q + \sqrt{2qc} + 2c$.

Also, the event that $h_S$ labels every held-out example correctly yet $\mathrm{err}_D(h_S) > 2c$ has probability at most $\delta$.

## Proof sketch

Conditioned on the kept examples, the held-out examples are independent draws from $D$, so $q$ is an average of at least $m - k$ Bernoulli trials with mean $\mathrm{err}_D(h_S)$. Apply Hoeffding's inequality, or the multiplicative Chernoff lower tail inverted at level $e^{-(m-k)c}$, for each possible index list and take a union bound over at most $(m+1)^k$ lists.

## Depends on

- [Labelled sample compression scheme](labelled-sample-compression-scheme.md)
- [Generalization bound for sample compression schemes](../../generalization-bounds-and-concentration/generalization-bound-for-sample-compression-schemes.md)

## Proof depends on

- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
- N. Littlestone and M. K. Warmuth, "Relating Data Compression and Learnability", unpublished manuscript, 1986.
- S. Floyd and M. K. Warmuth, "Sample Compression, Learnability, and the Vapnik-Chervonenkis Dimension", Machine Learning, 1995.
