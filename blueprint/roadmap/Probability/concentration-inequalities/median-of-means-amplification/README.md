# Median-of-means amplification

An estimator that is accurate with probability at least $7/8$ can be made accurate with probability
$1 - \varepsilon$ by taking the median of $O(\log(1/\varepsilon))$ independent copies: the median
leaves an interval only if at least half of the copies do, and a Chernoff or Hoeffding bound makes
that exponentially unlikely. Applied to means of independent copies of an unbiased estimator, whose
accuracy comes from Chebyshev's inequality, this is the median-of-means technique introduced for
streaming algorithms by N. Alon, Y. Matias and M. Szegedy, "The space complexity of approximating
the frequency moments", *J. Comput. System Sci.* 58 (1999) 137–147, proofs of Theorems 2.1 and 2.2.
With Hoeffding's inequality the median step gives the bound $e^{-9s/32}$ for $s$ copies.

- [Sample median](sample-median.md)
- [The median lies in an interval holding a strict majority](sample-median-mem-icc.md)
- [At least half of independent estimates are rarely bad](measure-real-two-mul-card-bad-ge-le.md)
- [Median amplification](measure-real-sample-median-not-mem-icc-l.md)

## Related topics

- [Hoeffding's inequality](../hoeffding-s-inequality/README.md): the tail bound used for the number of bad estimates.
- [Frequency moments of data streams](../../../ComputerScience/randomized-algorithms/frequency-moments-of-data-streams/README.md): the streaming estimator of Alon, Matias and Szegedy, where median of means was introduced.
