# Palindromes in residue classes: a logarithmic error bound

Let $b \ge 2$ be a natural
number, let $q$ be an odd natural number with $b \equiv 1 \pmod q$, and let $r$ be a natural
number with $r < q$. For natural numbers $m$, $q'$ and $r'$, write $A_b(m, q', r')$ for the number
of base-$b$ palindromes $n$ with $1 \le n \le m$ and $n \equiv r' \pmod{q'}$; thus $A_b(m, 1, 0)$
is the number of all base-$b$ palindromes in $[1, m]$. Then for every natural number $m \ge 1$,

$$\left| A_b(m, q, r) - \frac{A_b(m, 1, 0)}{q} \right| \le \frac{\log m}{2 \log b} + 2,$$

where $\log$ is the natural logarithm.

## Sources

- K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8, Corollary 12.
