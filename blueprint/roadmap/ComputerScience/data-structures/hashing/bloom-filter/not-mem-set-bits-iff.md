# A Bloom filter bit is unset iff no stored hash selects it

For every outcome $H$ of the stored hash values (with $n$ elements, $k$ hash functions and $m$
bits) and every bit $i \in \{0, \dots, m - 1\}$, the bit $i$ is not set by $H$ if and only if
$H(a, j) \ne i$ for every element $a$ and every hash function $j$.
