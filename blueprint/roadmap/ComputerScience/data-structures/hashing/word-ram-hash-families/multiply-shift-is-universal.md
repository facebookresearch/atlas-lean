# Multiply-shift is 2/2^M-universal

For all distinct $x, y \in [2^{w_0}]$ and $0 < M \le w_0$, if $a$ is uniform among the odd numbers below $2^{w_0}$ then

$$
\Pr_a\left[h_a(x) = h_a(y)\right] \le \frac{2}{2^M}.
$$

Consequently, mapping a set $W$ of keys by multiply-shift to $R$ bits is injective on $W$ except with probability at most $|W| (|W| - 1) / 2^R$.

## Proof sketch

Write $x - y = 2^i z$ with $z$ odd. Then $a(x-y) \bmod 2^{w_0}$ is $2^i$ times a uniformly random odd residue modulo $2^{w_0 - i}$, and a collision of the top $M$ bits forces this difference into an interval of length about $2^{w_0 - M + 1}$ around $0$ or $2^{w_0}$; counting odd residues in it gives the bound. The injectivity statement is a union bound over the $\binom{|W|}{2}$ pairs.

## Depends on

- [Multiply-shift hashing](multiply-shift-hashing.md)
- [k-wise independent hash family](k-wise-independent-hash-family.md)

## Sources

- M. Dietzfelbinger, T. Hagerup, J. Katajainen and M. Penttonen, "A Reliable Randomized Algorithm for the Closest-Pair Problem", Journal of Algorithms 25(1), 1997.
