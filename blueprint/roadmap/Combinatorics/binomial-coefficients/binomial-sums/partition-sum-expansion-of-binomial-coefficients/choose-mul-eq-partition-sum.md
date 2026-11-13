# Partition-sum expansion of $\binom{nm}{l}$

Let $n$ and $m$ be positive natural numbers and
let $l$ be a natural number with $1 \le l \le nm$. Let $P$ be the set of tuples
$s = (s_1, \dots, s_m)$ of natural numbers with $\sum_{j=1}^{m} j\,s_j = l$, and for $s \in P$
write $T_j(s) = s_{j+1} + \dots + s_m$. Then

$$\binom{nm}{l} = \sum_{s \in P} \prod_{j=1}^{m} \binom{n - T_j(s)}{s_j} \binom{m}{j}^{s_j},$$

where $n - T_j(s)$ is read as $0$ when $T_j(s) > n$.

## Sources

- Jocelyn Quaintance and Harris Kwong, "Permutations and Combinations of Colored Multisets," Journal of Integer Sequences 13 (2010), Article 10.2.6, Theorem, lines 329–336. <https://cs.uwaterloo.ca/journals/JIS/VOL13/Kwong/kwong6.tex>
