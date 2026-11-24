# Fuelled parser for linear μ-calculus token lists

Parsing of a token list of the linear μ-calculus encoding: it reads one formula from the front of
the list and returns it with the remaining tokens. The fuel bounds the recursion depth; decoding a
list of length $\ell$ uses fuel $\ell + 1$, which exceeds the number of tokens of every formula
encoded in the list. A token $\langle k, v\rangle$ whose tag $k$ is that of $\bot$, $\top$ or a
connective is read as that symbol whatever $v$ is; a token with an unknown tag makes parsing fail.
