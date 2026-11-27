# The symbolic store of a constant table

For a constant table $t : \mathbb{N} \to \mathbb{N} \cup \{\bot\}$, recording known values $t(x) = n$ of some variables, the symbolic store of $t$ maps a variable index $x$ to the constant $n$ when $t(x) = n$ and to the variable $x$ itself when $t(x) = \bot$.
