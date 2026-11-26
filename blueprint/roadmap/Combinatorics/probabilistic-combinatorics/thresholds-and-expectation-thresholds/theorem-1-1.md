# Thresholds versus fractional expectation-thresholds

There is an absolute real constant $K$ ([the constant of the theorem](k.md)) such that, for every finite set $X$ and every increasing
family $\mathcal F$ of subsets of $X$ (closed under taking supersets) with
$\ell(\mathcal F) \ge 2$, where $\ell(\mathcal F)$ is the size of a largest minimal element of
$\mathcal F$,

$$
p_c(\mathcal F) \le K \, q_f(\mathcal F) \log \ell(\mathcal F),
$$

where $p_c$ is the threshold, $q_f$ the fractional expectation-threshold and $\log$ the
natural logarithm.

The hypothesis $\ell(\mathcal F) \ge 2$ is not explicit in the paper but is needed: if
$\ell(\mathcal F) = 1$ then $\log \ell(\mathcal F) = 0$, while $p_c(\mathcal F) \in (0, 1)$,
so the inequality cannot hold.

## Sources

- Keith Frankston, Jeff Kahn, Bhargav Narayanan and Jinyoung Park, *Thresholds versus fractional expectation-thresholds*, Ann. of Math. 194(2) (2021). Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge, problem `annals_fractional_expectation_thresholds` of the lean-eval benchmark.
