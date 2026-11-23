# Probability that two genes are still apart after `t` coalescence events

**Probability that two genes are still apart after `t` coalescence events** (Tajima 1983):
under random joining, for `n ≥ 2` and `t ≤ n - 2`, it is
`∏_{i < t} (1 - 1 / C(n - i, 2)) = (n - t - 1)(n + 1) / ((n - t + 1)(n - 1))`, which is
`pairSeparateProb n (n - t)`; `integral_pairApart_randomJoining` states it in that form.
