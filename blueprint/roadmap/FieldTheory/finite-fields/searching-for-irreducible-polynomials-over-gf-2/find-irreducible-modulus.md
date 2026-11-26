# Exhaustive search for an irreducible binary modulus

For a width $s \ge 1$, the search runs through the $s$-bit words $g = (g_0, \dots, g_{s-1})$ in
increasing order of the integer $\sum_{i < s} g_i 2^i$ and returns the first one that passes the
[exhaustive inverse test](passes-inverse-test.md), that is, the first one whose monic modulus
$X^s + \sum_{i < s} g_i X^i$ is irreducible over $\mathbb{F}_2$; it reports failure if there is
none. At width $s = 0$ it reports failure without searching.
