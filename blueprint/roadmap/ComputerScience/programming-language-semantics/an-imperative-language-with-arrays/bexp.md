# Boolean expressions of the imperative language with arrays

The Boolean expressions are built inductively from the constant true and the comparisons
$e_1 \le e_2$ of arithmetic expressions: if $b$, $b_1$ and $b_2$ are Boolean expressions, then so are
the conjunction $b_1 \wedge b_2$ and the negation $\neg b$.

Unlike [the Boolean expressions of IMP](../operational-semantics-of-imp/bexp.md), they have no equality test and no
constant false, which are expressible with $\le$ and negation.
