# Evaluation of arithmetic expressions in the imperative language with arrays

The value $e(s) \in \mathbb{N}$ of an arithmetic expression $e$ in a state $s$ is defined by recursion on $e$: a numeral $n$ has value $n$, a variable $x$ has value $s(x)$, and

$$(e_1 + e_2)(s) = e_1(s) + e_2(s), \qquad (e_1 - e_2)(s) = e_1(s) \mathbin{\dot-} e_2(s),$$

$$(e_1 \cdot e_2)(s) = e_1(s) \cdot e_2(s), \qquad (e_1 / e_2)(s) = \lfloor e_1(s) / e_2(s) \rfloor.$$

Arithmetic is on the natural numbers: subtraction truncates at zero ($m \mathbin{\dot-} n = 0$ when $m \le n$) and division by zero gives $0$.
