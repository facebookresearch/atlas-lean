# Probability that a random subset avoids a given set

If the random subset $R$ contains each element $a$ independently with probability $p(a)$, then for every finite $S$,

$$\Pr[S \cap R = \emptyset] = \prod_{a \in S} \bigl(1 - p(a)\bigr).$$

For $G(n, p)$ and the pairs inside a $k$-set this is $(1-p)^{\binom k2}$, the probability that the $k$-set is independent.

## Sources

- Yufei Zhao (lecturer) and Andrew Lin (notes), *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, proof of Theorem 1.4 (the case $p = 1/2$).
