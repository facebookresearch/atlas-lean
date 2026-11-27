# Arithmetic expressions of the imperative language with arrays

The arithmetic expressions are built inductively from the numerals $n$, one for each natural number
$n$, and the variables, named by strings: if $e_1$ and $e_2$ are arithmetic expressions, then so are
$e_1 + e_2$, $e_1 - e_2$, $e_1 \cdot e_2$ and $e_1 / e_2$. They are evaluated in natural-number
arithmetic, where subtraction truncates at zero and division by zero gives zero.

Unlike [the arithmetic expressions of IMP](../operational-semantics-of-imp/aexp.md), whose variables are indexed by
natural numbers, they include division.
