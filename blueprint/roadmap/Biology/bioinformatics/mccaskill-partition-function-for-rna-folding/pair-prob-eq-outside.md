# McCaskill's base-pair probabilities

For real weights $w$ and positions $i, j$ with $i + m < j$ that [can pair](can-pair.md),

$$P(i, j) = \frac{\bar Z(i, j)\, w(i, j)\, Z(i + 1, j - i - 1)}{Z(0, n)},$$

where $P$ is the [base-pair probability](pair-prob.md), $\bar Z$ the [outside value](outside.md), $Z$ the [inside value](inside.md) and $n$ the length of the sequence, with $x/0 = 0$.
