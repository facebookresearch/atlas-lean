# Randomization probability of the detection test

For a natural number $n$ and reals $p_0, \mathrm{FPR}$, with $k$ the [critical count](critical-count.md), the randomization probability is

$$d = \frac{\mathrm{FPR} - P_{p_0}(k)}{P_{p_0}(k - 1) - P_{p_0}(k)},$$

where $P_{p_0}$ is the [upper tail](upper-tail.md), $k - 1$ is truncated at $0$, and $x/0 = 0$.
