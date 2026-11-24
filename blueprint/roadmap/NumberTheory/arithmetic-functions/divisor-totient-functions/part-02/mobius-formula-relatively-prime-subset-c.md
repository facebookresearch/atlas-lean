# Relatively prime subset counts

Let $\ell < m$ and $k \ge 1$ be natural numbers, and let
$\mu$ be the Möbius function. The number of nonempty subsets of $\{\ell + 1, \dots, m\}$ whose
elements have greatest common divisor $1$ is

$$\sum_{d=1}^{m} \mu(d) \left(2^{\lfloor m/d \rfloor - \lfloor \ell/d \rfloor} - 1\right),$$

and the number of $k$-element subsets of $\{\ell + 1, \dots, m\}$ whose elements have greatest
common divisor $1$ is

$$\sum_{d=1}^{m} \mu(d) \binom{\lfloor m/d \rfloor - \lfloor \ell/d \rfloor}{k}.$$

## Sources

- M. Ayad, V. Coia, and O. Kihel, “The Number of Relatively Prime Subsets of a Finite Union of Sets of Consecutive Integers”, Journal of Integer Sequences 17 (2014), Article 14.3.7, Theorem 1, lines 138-151, <https://cs.uwaterloo.ca/journals/JIS/VOL17/Kihel/kihel10.tex>.
