# Counting palindromes up to $m$ and by parity

Let $b \ge 2$ and $m \ge 1$, and write
$m = (a_k a_{k-1} \cdots a_0)_b$ in base $b$, with leading digit $a_k \ne 0$. For natural numbers
$q$ and $r$, let $A_b(m, q, r)$ be the number of $b$-adic palindromes $n$ with $1 \le n \le m$
and $n \equiv r \pmod q$, and let $C_b(m)$ be the palindromic half copy of $m$. Put $\delta = 1$
if $C_b(m) \le m$ and $\delta = 0$ otherwise. Then
$A_b(m, 1, 0) = b^{\lceil k/2 \rceil} +
\sum_{i=0}^{\lfloor k/2 \rfloor} a_{k-i} b^{\lfloor k/2 \rfloor - i} + \delta - 2$.
If moreover $b$ is even, let
$\alpha = (b^{\lceil k/2 \rceil} + b^{\lfloor k/2 \rfloor} - 2)/(b - 1)$ and
$S = \sum_{i=1}^{\lfloor k/2 \rfloor} a_{k-i} b^{\lfloor k/2 \rfloor - i}$, let $\varepsilon_0 = 1$
if $a_k$ is even and $\varepsilon_0 = 0$ otherwise, and let $\varepsilon_1 = 1 - \varepsilon_0$.
Then $A_b(m, 2, 0) = (b/2 - 1)\alpha + \lfloor (a_k - 1)/2 \rfloor b^{\lfloor k/2 \rfloor} +
\varepsilon_0 (S + \delta)$ and
$A_b(m, 2, 1) = b\alpha/2 + \lceil (a_k - 1)/2 \rceil b^{\lfloor k/2 \rfloor} +
\varepsilon_1 (S + \delta)$.

## Sources

- K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8, Corollary 8.
