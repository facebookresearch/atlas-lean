# Polynomial-size token-list encoding of μ-calculus formulas

A token-list encoding of μ-calculus formulas with atoms in $\mathbb{N}$, of polynomial size. With
the pairing function $\langle a, b\rangle$ of the pairing code, each connective contributes one
token $\langle k, 0\rangle$ for a small tag $k$, and each atom or variable with index $v$ one token
$\langle k, v\rangle$, of binary size $O(1 + \log(v + 1))$. Written as a bit string in which each
token is delimited, the encoding of a formula has length linear in the number of its syntax nodes
plus the total binary size of its atom labels and variable indices. For example $\Box^d p_0$ is
encoded by $d + 1$ tokens, whereas the binary length of its pairing code is exponential in $d$.
