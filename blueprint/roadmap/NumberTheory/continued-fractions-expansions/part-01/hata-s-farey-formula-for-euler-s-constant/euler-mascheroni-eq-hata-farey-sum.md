# Hata's formula for Euler's constant

Let $S$ be the set of quadruples $(a, b, c, d)$ of
natural numbers with $bc = ad + 1$, $a > 0$ and $c \le d$; these are the Farey intervals
$[a/b, c/d] \subseteq [0, 1]$ with positive left endpoint. The family
$1/(abcd(a + c)(b + d))$, indexed by $(a, b, c, d) \in S$, is summable, and Euler's constant
$\gamma$ satisfies

$$
\gamma = \frac{1}{2} + \frac{1}{2} \sum_{(a, b, c, d) \in S} \frac{1}{abcd(a + c)(b + d)}.
$$

The set $S$ is the source's $F \setminus F^*$, where $F^*$ consists of the intervals $[0/1, 1/n]$.

## Sources

- Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Theorem 1, attributed there to Hata.
