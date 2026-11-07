# Lucky spots of weakly decreasing parking functions as a sum

Number the cars and spots
$0, \dots, n-1$. For cars $i$ and spots $j$, let $q^d_n(i, j)$ be the number of weakly decreasing
parking functions $f$ of length $n$ (that is, $f(0) \ge f(1) \ge \dots \ge f(n-1)$) with
$f(i) = j$ in which car $i$ is lucky. Then for every spot $j$,

$$\sum_{i=0}^{n-1} q^d_n(i, j) = \sum_{i=1}^{n-j} \frac{(n-i-j+1)^2}{(n+1-i)(n-j)}
\binom{n-i+j}{j} \binom{n-j+i-2}{i-1}.$$

The left side counts the weakly decreasing parking functions in which spot $j$ is lucky, that
is, taken by a car that prefers it.

## Sources

- Steve Butler et al., "Lucky Cars and Lucky Spots in Parking Functions", Corollary 23.
