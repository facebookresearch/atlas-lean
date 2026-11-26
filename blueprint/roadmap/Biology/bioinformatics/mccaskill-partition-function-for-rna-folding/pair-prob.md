# Base-pair probability

For real weights $w$ and positions $i, j$, the base-pair probability is

$$P(i, j) = \frac{\sum_{P \ni (i, j)} \prod_{(a, b) \in P} w(a, b)}{\sum_{P} \prod_{(a, b) \in P} w(a, b)},$$

sums over the [secondary structures](structures.md) (containing $(i, j)$ in the numerator), with the convention $x/0 = 0$. For nonnegative weights the denominator is [at least one](one-le-sum-weight.md); for Boltzmann weights it is the probability of $(i, j)$ under the Boltzmann distribution on structures.
