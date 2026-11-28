# The constant of the Frankston–Kahn–Narayanan–Park theorem

One choice of the universal constant in the [fractional expectation-threshold bound](theorem-1-1.md)
is $K=12/\ln 2$, when the logarithm is natural and the largest minimal size $\ell$ is at least two.
This is not a claim of optimality.

Park and Vondrák prove the finite bound $p_c\le 6q_c\log_2(2\ell)$ for the **integral**
expectation-threshold $q_c$. Apply it to the minimal members of the increasing family: their
upward closure is the original family, and each has size at most $\ell$. An integral cover's
indicator is a fractional cover of exactly the same cost, so $q_c\le q_f$. Finally,
$\ln(2\ell)=\ln 2+\ln\ell\le 2\ln\ell$ for every $\ell\ge2$, including equality at $\ell=2$.

## Sources

- Keith Frankston, Jeff Kahn, Bhargav Narayanan and Jinyoung Park, [*Thresholds versus fractional expectation-thresholds*](https://doi.org/10.4007/annals.2021.194.2.2), Ann. of Math. 194(2) (2021), Theorem 1.1 and (3). Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge, problem `annals_fractional_expectation_thresholds` of the lean-eval benchmark.
- Bryan Park and Jan Vondrák, [*A simple proof of the non-uniform Kahn–Kalai conjecture*](https://arxiv.org/abs/2306.12576), §2.3, the estimate with $L=6$ on p. 6.
