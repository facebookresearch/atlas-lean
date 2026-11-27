# Exhaustive inverse test for a binary polynomial modulus

Fix a width $s \in \mathbb{N}$. An $s$-bit word $w = (w_0, \dots, w_{s-1})$ encodes the polynomial
$w(X) = \sum_{i < s} w_i X^i$ over $\mathbb{F}_2$, and a word $g$ encodes the monic modulus
$m_g(X) = X^s + g(X)$ of degree $s$. The inverse test of $g$ tries all pairs of $s$-bit words and
succeeds when every nonzero word $x$ has a word $y$ with $x(X)\, y(X) \equiv 1 \pmod{m_g}$, that is,
when every nonzero residue modulo $m_g$ is invertible.

At width $s = 0$ the only word is zero, so the test succeeds although $m_g = 1$ is not irreducible.
