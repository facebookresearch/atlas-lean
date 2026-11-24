# The fingerprint error count

Let $K$ be a field, $S$ a finite set of monic irreducible polynomials of degree $k$ over $K$, and
$(g_i)_{i \in I}$ a finite family of polynomials over $K$. Then

$$\#\{f \in S : f \mid g_i \text{ for some } i \in I \text{ with } g_i \ne 0\} \cdot k
  \le \sum_{i \in I} \deg g_i.$$

In Rabin's string-matching algorithm the pattern $x_1 \dots x_n$ and the text windows
$y_i \dots y_{i+n-1}$ are read as polynomials $a(t)$ and $a_i(t)$ of degree less than $n$ over
$\mathbb{Z}_2$, and a modulus $p(t)$ reports a false match at window $i$ exactly when
$a \ne a_i$ and $p \mid a - a_i$. With $g_i = a - a_i$ the bound says that at most $nm/k$ of the
irreducible moduli of degree $k$ produce any error on a text of length $m$ (Rabin's
$\ell k = \deg P \le \deg H \le nm$). When $k$ is prime there are $(2^k - 2)/k$ such moduli, and dividing by this number gives the error probability of his Theorem 3.

## Informally uses

- [At most deg H / k irreducible factors of degree k](card-filter-dvd-mul-le-nat-degree.md),
  applied to the product of the nonzero $g_i$.

## Background

- [Monic irreducible polynomials of prime degree over Z2](ncard-monic-irreducible-zmod-two-of-prim.md):
  the number of moduli the algorithm chooses from.

## Sources

- M. O. Rabin, *Fingerprinting by random polynomials*, Technical Report TR-15-81, Center for Research in Computing Technology, Harvard University, 1981, Section 4, Theorem 3 and its proof, equations (5) and (6).
