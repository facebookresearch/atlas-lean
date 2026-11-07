# Palindromes up to a power of the base in residue classes

Let $b \ge 2$, $k \ge 1$ and
$q \ge 1$ be natural numbers and let $r$ be a natural number with $r < q$. Write $A_b(m, q, r)$
for the number of base-$b$ palindromes $n$ with $1 \le n \le m$ and $n \equiv r \pmod q$, and
$[r = 0]$ for $1$ if $r = 0$ and $0$ otherwise. If $q \mid b$, then

$$A_b(b^k, q, r) = \left(\frac{b}{q} - [r = 0]\right)
\frac{b^{\lceil k/2 \rceil} + b^{\lfloor k/2 \rfloor} - 2}{b - 1}.$$

If $b \equiv 1 \pmod q$, then $A_b(b^k, q, r)$ equals
$(b^{\lceil k/2 \rceil} + b^{\lfloor k/2 \rfloor} - 2)/q$ if $q$ is odd,
$(b - 1) b^{\lfloor (k-1)/2 \rfloor}/q$ if $q$ is even and $r$ is odd, and
$((b + 1) b^{\lfloor (k-1)/2 \rfloor} + 2 b^{\lfloor k/2 \rfloor} - 4)/q$ if $q$ and $r$ are both
even. All these identities hold as identities of rational numbers.

## Sources

- K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8, Corollary 11.
