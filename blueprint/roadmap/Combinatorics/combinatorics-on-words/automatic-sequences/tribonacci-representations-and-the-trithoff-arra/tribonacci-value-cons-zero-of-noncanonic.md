# Appending a zero to a non-canonical Tribonacci representation

Let $T_0 = T_1 = 0$,
$T_2 = 1$ and $T_{k+3} = T_{k+2} + T_{k+1} + T_k$ be the Tribonacci numbers, and for a digit
word $u$, written most significant digit first, let $[u]_T$ be its Tribonacci value, in which
the $i$-th digit from the right (counting from $0$) weighs $T_{i+3}$. Let $w$ be a digit word
with all digits in $\{0, 1\}$ (three consecutive ones are allowed) and $[w]_T = n$, and let $v$
be a Tribonacci representation of $n$. Then $[w0]_T = [v0]_T$, where $w0$ and $v0$ are $w$ and
$v$ followed by the digit $0$; that is, $w0$ evaluates to the Tribonacci successor
$\mathrm{out}(n) = [v0]_T$ of $n$.

## Sources

- E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Lemma 12 (`jis-2025-25.5.4-lem-12`).
