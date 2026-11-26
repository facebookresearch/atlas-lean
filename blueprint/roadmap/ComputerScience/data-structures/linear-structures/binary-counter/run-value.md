# Counter value after successive increments

For every width $k$, every $k$-bit counter $b$
and every $n$, let $v$ be the value of $b$ read as an unsigned binary number with the least
significant bit first. After $n$ successive increments starting from $b$, the counter read the
same way has value $(v + n) \bmod 2^k$.
