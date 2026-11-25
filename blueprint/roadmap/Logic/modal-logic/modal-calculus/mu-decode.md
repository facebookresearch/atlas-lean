# Decoding a μ-calculus number code to a formula

Decoding of natural numbers into μ-calculus formulas: a number $c$ is decoded with fuel $c + 1$. It
is a partial inverse of the pairing code. Decoding the code of a formula returns the formula, but
the decoder ignores the second component of the pairs it reads for $\bot$ and $\top$, so it also
accepts numbers that are not codes: for example $\langle 3, 1\rangle = 13$ decodes to $\bot$, whose
code is $\langle 3, 0\rangle = 12$. Numbers whose first component is not a tag of the encoding are
rejected.
