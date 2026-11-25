# Outside recursion

For a sequence $s$ of length $n$ and positions $i, j$, the outside value is defined by

$$\bar Z(i, j) = Z(0, i)\, Z(j + 1, n'_j) + \sum_{a=0}^{i-1} \sum_{c=0}^{n'_j - 1} [\,a + m < b,\ a \text{ and } b \text{ can pair}\,]\; \bar Z(a, b)\, w(a, b)\, Z(a + 1, i - a - 1)\, Z(j + 1, c),$$

where $b = j + 1 + c$, $n'_j = \max(n - j - 1, 0)$ and $Z$ is the [inside value](inside.md) (McCaskill 1990): either no pair encloses $(i, j)$, or there is a unique innermost enclosing pair $(a, b)$.

## Sources

- J. S. McCaskill, *The equilibrium partition function and base pair binding probabilities for RNA secondary structure*, Biopolymers 29 (1990), 1105–1119.
