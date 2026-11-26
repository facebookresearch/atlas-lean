# Veltkamp splitting of a floating-point number

Work in binary floating-point arithmetic with $p$-bit significands, $p \ge 3$, an unbounded exponent range and [rounding to nearest with ties to even](fl.md), writing $\mathrm{fl}$ for the rounded result of an operation. Let $a$ be a [floating-point number](is-float.md) and choose an integer splitting point $s$ with $p/2 \le s \le p - 1$. The algorithm

$$c = \mathrm{fl}\bigl((2^s + 1)\, a\bigr), \quad a_{\mathrm{big}} = \mathrm{fl}(c - a), \quad a_{\mathrm{hi}} = \mathrm{fl}(c - a_{\mathrm{big}}), \quad a_{\mathrm{lo}} = \mathrm{fl}(a - a_{\mathrm{hi}})$$

produces floating-point numbers with

$$a = a_{\mathrm{hi}} + a_{\mathrm{lo}}, \qquad |a_{\mathrm{hi}}| \ge |a_{\mathrm{lo}}|,$$

where $a_{\mathrm{hi}}$ is representable with a $(p - s)$-bit significand, $a_{\mathrm{lo}}$ with an $(s - 1)$-bit significand, and $a_{\mathrm{hi}}$ and $a_{\mathrm{lo}}$ are nonoverlapping. Here two floating-point numbers $x$ and $y$ are *nonoverlapping* if there are integers $r$ and $t$ with $x = r2^t$ and $|y| < 2^t$, or $y = r2^t$ and $|x| < 2^t$, so that zero overlaps no number; they are *nonadjacent* if none of the pairs $(x, y)$, $(2x, y)$, $(x, 2y)$ overlaps. For nonzero numbers, nonoverlapping means that the least significant nonzero bit of one is more significant than the most significant nonzero bit of the other; for $a = 1$ the splitting is $(1, 0)$. With $s = \lceil p/2 \rceil$ both halves have at most $\lfloor p/2 \rfloor$ bits, which the sign of $a_{\mathrm{lo}}$ makes possible; for example the seven-bit number $1001001$ splits into $1010000$ and $-111$.

## Depends on

- [Binary floating-point numbers](is-float.md)
- [Round to nearest, ties to even](fl.md)

## Proof depends on

- [Sterbenz's lemma](is-float-sub.md)
- [The relative error bound](abs-fl-sub-le.md)

## Sources

- J. R. Shewchuk, "Adaptive precision floating-point arithmetic and fast robust geometric predicates", *Discrete & Computational Geometry* 18(3):305–363, 1997; technical report version CMU-CS-96-140R, Section 2.5, Theorem 17 (first proven by Dekker) with the algorithm SPLIT and its proof, which uses Lemma 5 (Sterbenz); Section 2.1 for the model (radix two, exact rounding, overflow and underflow not addressed) and the definition of nonoverlapping values. <https://people.eecs.berkeley.edu/~jrs/papers/robustr.pdf>
