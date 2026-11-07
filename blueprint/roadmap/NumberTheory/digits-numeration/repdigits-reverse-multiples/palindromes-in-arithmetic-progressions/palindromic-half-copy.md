# Palindromic half copy

For natural numbers $b$ and $m \ge 1$, write
$m = (a_k a_{k-1} \cdots a_0)_b$ for the base-$b$ digits of $m$. The palindromic half copy of $m$
is $C_b(m) = \sum_{j=0}^{k} a_{\max(j, k - j)} b^j$: the $b$-adic palindrome with the same number
of digits as $m$ whose upper digits $a_k, \dots, a_{\lceil k/2 \rceil}$ are those of $m$ and whose
lower digits mirror them. For $m = 0$, which has no digits, $C_b(0) = 0$.

## Sources

- K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8, Definition 1.
