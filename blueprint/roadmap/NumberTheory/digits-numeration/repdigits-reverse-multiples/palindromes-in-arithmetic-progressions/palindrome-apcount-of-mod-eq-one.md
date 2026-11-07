# Palindromes in residue classes modulo a divisor of the base minus one

Let $b \ge 2$,
$m \ge 1$ and $q \ge 1$ be natural numbers with $b \equiv 1 \pmod q$, and let $r$ be a natural
number with $r < q$. Write $m = (a_k a_{k-1} \cdots a_0)_b$ in base $b$. Write $A_b(m, q, r)$ for
the number of base-$b$ palindromes $n$ with $1 \le n \le m$ and $n \equiv r \pmod q$, $C_b(m)$
for the palindromic half copy of $m$, $[P]$ for $1$ if $P$ holds and $0$ otherwise, and
$t \bmod d$ for the least nonnegative residue of an integer $t$ modulo a positive integer $d$.
For $j \ge 0$ define integers $s_j$ and $r_j$ as follows. If $q$ is even and $2j \ne k$, let
$s_j = a_{k-j} \bmod (q/2)$ and
$r_j = \bigl(\lfloor r/2 \rfloor - \sum_{i=0}^{j-1} a_{k-i}\bigr) \bmod (q/2)$. If $q$ is odd
and $2j \ne k$, let $s_j = a_{k-j} \bmod q$ and
$r_j = \bigl(\frac{q+1}{2} r - \sum_{i=0}^{j-1} a_{k-i}\bigr) \bmod q$. If $2j = k$, let
$s_j = a_{k-j} \bmod q$ and $r_j = \bigl(r - 2 \sum_{i=0}^{k/2-1} a_{k-i}\bigr) \bmod q$. Put
$\delta = [C_b(m) \le m] \, [r_{\lfloor k/2 \rfloor} = s_{\lfloor k/2 \rfloor}]$ and

$$m_1^* = \sum_{j=0}^{\lfloor (k-1)/2 \rfloor}
\left( \frac{2 a_{k-j} b^{\lfloor (k-1)/2 \rfloor - j} - 2 s_j}{q} + [r_j < s_j] \right),$$



$$m_2^* = \sum_{j=0}^{\lfloor k/2 \rfloor - 1}
\frac{a_{k-j} (b - 1) b^{\lfloor k/2 \rfloor - j - 1}}{q},$$



$$m_3^* = \sum_{j=0}^{\lfloor k/2 \rfloor - 1}
\left( \frac{a_{k-j} (b + 1) b^{\lfloor k/2 \rfloor - j - 1} - 2 s_j}{q} + [r_j < s_j] \right).$$

Then, as rational numbers, if $q$ is odd,

$$A_b(m, q, r) = \frac{b^{\lfloor (k+1)/2 \rfloor} - 1}{q} +
\sum_{j=0}^{\lfloor k/2 \rfloor} \left( \left\lfloor \frac{a_{k-j} b^{\lfloor k/2 \rfloor - j}}{q}
\right\rfloor + [r_j < s_j] \right) - [r = 0] + \delta,$$

and if $q$ is even, $A_b(m, q, r)$ equals $(b - 1) b^{(k-1)/2}/q$ when $k$ and $r$ are odd,
$((b + 1) b^{(k-1)/2} - 2)/q + m_1^* - [r = 0] + \delta$ when $k$ is odd and $r$ is even,
$\lfloor a_{k/2}/q \rfloor + m_2^* + [r_{k/2} < s_{k/2}] + \delta$ when $k$ is even and $r$ is
odd, and $2(b^{k/2} - 1)/q + \lfloor a_{k/2}/q \rfloor + m_3^* - [r = 0] +
[r_{k/2} < s_{k/2}] + \delta$ when $k$ and $r$ are both even.

## Sources

- K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8, Theorem 9.
