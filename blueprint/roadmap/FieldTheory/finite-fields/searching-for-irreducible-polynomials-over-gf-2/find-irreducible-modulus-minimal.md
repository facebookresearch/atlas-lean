# Minimality of the binary modulus found by exhaustive search

If the [exhaustive search](find-irreducible-modulus.md) at width $s$ returns the word
$g = (g_0, \dots, g_{s-1})$, then $g$ is the smallest $s$-bit word, read as the integer
$\sum_{i < s} g_i 2^i$, whose monic modulus is irreducible: for every $s$-bit word $g'$ such that
$X^s + \sum_{i < s} g'_i X^i$ is irreducible over $\mathbb{F}_2$,
$\sum_{i < s} g_i 2^i \le \sum_{i < s} g'_i 2^i$.
