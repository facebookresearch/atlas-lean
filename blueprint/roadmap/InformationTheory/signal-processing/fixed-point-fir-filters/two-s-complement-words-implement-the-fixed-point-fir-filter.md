# Two's-complement words implement the fixed-point FIR filter

Let $w \ge 1$ and decode a $w$-bit word $u = (u_{w-1} \dots u_0)$ as the integer $\operatorname{dec}(u) = -u_{w-1}2^{w-1} +
\sum_{i < w-1} u_i 2^i$, so that $\operatorname{dec}$ is a bijection onto $[-2^{w-1}, 2^{w-1})$. Word addition and multiplication
are integer addition and multiplication modulo $2^w$, and an operation sets its signed-overflow flag when the integer result of
the operation on the decoded operands lies outside $[-2^{w-1}, 2^{w-1})$. Run the
[fixed-point FIR filter](error-bound-for-a-fixed-point-fir-filter.md) at scale $2^{-q}$ on integers, representing a grid value
$v$ by $2^q v$: products of scaled integers are formed exactly, rounded half up by $u \mapsto \lfloor (u + 2^{q-1}) / 2^q \rfloor$
(the identity when $q = 0$), and accumulated by addition, with $0 \le q < w$ and the overflow flag raised when a stored scaled
value leaves $[-2^{w-1}, 2^{w-1})$. Implement it on
$w$-bit words, forming products in $2w$-bit words and rounding them, when $q \ge 1$, by adding $2^{q-1}$ and shifting right arithmetically by $q$ (no rounding when $q = 0$).
Then at every step of the fold the decoded word equals the integer filter's value whenever no flag has been raised so far, and a
word flag is raised at a step exactly when the integer value at that step leaves the $w$-bit range. Hence, if no flag is raised,
the word filter's decoded output is $2^q \hat y$, and $\hat y$ obeys the error bound of the fixed-point filter.

Each step reduces to two facts about $w$-bit words: $\operatorname{dec}$ of the wrapped sum or product equals the integer result
when that result is in range, and the signed-overflow flag detects exactly the out-of-range results. A product of two $w$-bit
values always fits in $2w$ bits.

## Depends on

- [Error bound for a fixed-point FIR filter](error-bound-for-a-fixed-point-fir-filter.md)

## Sources

- D. A. Patterson and J. L. Hennessy, *Computer Organization and Design: The Hardware/Software Interface*, 5th edition, Morgan Kaufmann, 2014, Chapter 3 (two's-complement arithmetic and overflow).
- A. V. Oppenheim and R. W. Schafer, *Discrete-Time Signal Processing*, 3rd edition, Pearson, 2010, Chapter 6 (fixed-point realizations of digital filters).
