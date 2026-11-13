# Boundary values of lucky-car counts (Lemma 9)

Let $n \ge 1$, number the cars and spots
$0, \dots, n-1$, and let $q_n(i, j)$ be the number of parking functions of length $n$ in which
car $i$ prefers spot $j$ and is lucky. Then for all $i, j \in \{0, \dots, n-1\}$, with powers
taken in $\mathbb{Q}$ (the integer exponents may be negative),

$$q_n(n-1, j) = \binom{n-1}{j} (j+1)^{j-1} (n-j)^{n-j-2},$$



$$q_n(0, j) = \sum_{k=j+1}^{n} \binom{n-1}{k-1} k^{k-2} (n-k+1)^{n-k-1},$$



$$q_n(i, n-1) = n^{n-2},$$



$$q_n(i, 0) = (n+1)^{n-i-2}\, n^{i-1}\, (2n-i).$$

In the one-based indexing of the source, car $i$ and spot $j$ here are car $i+1$ and spot $j+1$.

## Sources

- Steve Butler et al., "Lucky Cars and Lucky Spots in Parking Functions", Lemma 9.
