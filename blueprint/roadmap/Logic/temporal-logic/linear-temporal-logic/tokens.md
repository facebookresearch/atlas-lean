# Token encoding of an LTL formula

The prefix-order list of tokens of an LTL formula with atoms in $\mathbb{N}$. Tokens are natural
numbers $\langle k, a\rangle$, for the pairing function $\langle a, b\rangle = b^2 + a$ if $a < b$ and
$\langle a, b\rangle = a^2 + a + b$ otherwise: $\langle 0, a\rangle$ for the atom $a$, and
$\langle k, 0\rangle$ for truth ($k = 1$), negation ($2$), conjunction ($3$), next ($4$) and until
($5$), each followed by the tokens of its arguments.
