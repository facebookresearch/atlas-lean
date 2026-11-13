# Counting digit tuples by their sum modulo a divisor of the base minus one

Let $a$, $b$,
$k$ and $q$ be natural numbers, all at least $1$, with $b \equiv 1 \pmod q$, and let $r$ be an
integer. For natural numbers $x$ and $y$ write $N_b(k, q, r, x, y)$ for the number of tuples
$(x_1, \dots, x_k)$ of natural numbers with $x \le x_1 < y$, $x_i < b$ for $2 \le i \le k$, and
$x_1 + \dots + x_k \equiv r \pmod q$. Write $[P]$ for $1$ if $P$ holds and $0$ otherwise,
$\lfloor a/q \rfloor$ for the integer part of $a/q$, and $r \bmod q$ and $a \bmod q$ for the least
nonnegative residues modulo $q$. Then, as rational numbers,

$$N_b(k, q, r, 0, b) = \frac{b^k - 1}{q} + [r \equiv 0 \pmod q],$$



$$N_b(k, q, r, 1, b) = \frac{b^k - b^{k-1}}{q},$$



$$N_b(k, q, r, 0, a) = \frac{a (b^{k-1} - 1)}{q} + \lfloor a/q \rfloor + [r \bmod q < a \bmod q],$$



$$N_b(k, q, r, 1, a) = \frac{(a - 1)(b^{k-1} - 1)}{q} + \lfloor a/q \rfloor +
[r \bmod q < a \bmod q] - [r \equiv 0 \pmod q].$$

## Sources

- K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8, Lemma 5.
