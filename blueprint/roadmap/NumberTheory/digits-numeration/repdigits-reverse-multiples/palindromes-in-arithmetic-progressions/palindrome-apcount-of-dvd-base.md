# Palindromes in residue classes modulo a divisor of the base

Let $b \ge 2$, $m \ge 1$ and
$q \ge 1$ be natural numbers with $q \mid b$. Write $m = (a_k a_{k-1} \cdots a_0)_b$ in base $b$,
with leading digit $a_k$. Write $A_b(m, q, r)$ for the number of base-$b$ palindromes $n$ with
$1 \le n \le m$ and $n \equiv r \pmod q$, $C_b(m)$ for the palindromic half copy of $m$, and
$[P]$ for $1$ if $P$ holds and $0$ otherwise. Put

$$\alpha = \frac{b^{\lceil k/2 \rceil} + b^{\lfloor k/2 \rfloor} - 2}{b - 1}, \quad
S = \sum_{i=1}^{\lfloor k/2 \rfloor} a_{k-i} b^{\lfloor k/2 \rfloor - i}, \quad
\delta = [C_b(m) \le m].$$

Then, as rational numbers,

$$A_b(m, q, 0) = \left(\frac{b}{q} - 1\right) \alpha +
\left\lfloor \frac{a_k - 1}{q} \right\rfloor b^{\lfloor k/2 \rfloor} +
[a_k \equiv 0 \pmod q] (S + \delta),$$

and for every natural number $r$ with $r \bmod q > 0$,

$$A_b(m, q, r) = \frac{b \alpha}{q} +
\left\lceil \frac{a_k - (r \bmod q)}{q} \right\rceil b^{\lfloor k/2 \rfloor} +
[a_k \equiv r \pmod q] (S + \delta).$$

## Sources

- K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8, Theorem 7.
