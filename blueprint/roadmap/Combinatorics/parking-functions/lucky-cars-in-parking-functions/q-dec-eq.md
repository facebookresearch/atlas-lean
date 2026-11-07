# Decreasing lucky-car counts (Lemma 22)

Number the cars and spots $0, \dots, n-1$, and let
$q^{\mathrm{dec}}_n(i, j)$ be the number of weakly decreasing parking functions of length $n$ in
which car $i$ prefers spot $j$ and is lucky. For all $i, j \in \{0, \dots, n-1\}$, if $i + j < n$
then

$$q^{\mathrm{dec}}_n(i, j) = \frac{(n-i-j)^2}{(n-i)(n-j)} \binom{n-i+j-1}{j} \binom{n-j+i-1}{i},$$

and $q^{\mathrm{dec}}_n(i, j) = 0$ otherwise.

In the one-based indexing of the source the condition reads $i + j \le n + 1$.

## Sources

- Steve Butler et al., "Lucky Cars and Lucky Spots in Parking Functions", Lemma 22.
