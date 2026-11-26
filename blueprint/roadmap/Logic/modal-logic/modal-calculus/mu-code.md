# Pairing number code of a μ-calculus formula

An injective encoding of μ-calculus formulas with atoms in $\mathbb{N}$ as natural numbers, built
with the pairing function $\langle a, b\rangle = b^2 + a$ if $a < b$ and
$\langle a, b\rangle = a^2 + a + b$ otherwise (not Cantor's pairing). It is a coding of formulas by numbers, not an input encoding for complexity
statements: pairing squares the code at every unary connective, so the binary length of the code
of $\Box^d p_0$ roughly doubles at each $\Box$ and is exponential in $d$. The token encoding is the
one used for complexity.
