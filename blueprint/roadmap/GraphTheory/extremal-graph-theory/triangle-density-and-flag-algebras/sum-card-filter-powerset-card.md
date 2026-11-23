# Double counting $k$-sets inside $l$-sets

Let $V$ be a finite set with $n$ elements, $P$ a property of subsets of $V$, and $k \le l$ natural numbers. Then

$$\sum_{\substack{L \subseteq V \\ \lvert L\rvert = l}} \#\{K \subseteq L : \lvert K\rvert = k,\ P(K)\} = \binom{n - k}{l - k} \#\{K \subseteq V : \lvert K\rvert = k,\ P(K)\}:$$

every $k$-set with property $P$ is counted once for each of the $\binom{n-k}{l-k}$ sets of size $l$ containing it.
