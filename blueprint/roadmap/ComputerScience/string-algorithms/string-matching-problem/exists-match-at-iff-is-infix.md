# A pattern occurs in a text iff it matches at some offset

For lists $p$ and $t$, there
is an offset $k$ such that the pattern $p$ matches the text $t$ at $k$ if and only if $p$ is an
infix of $t$, that is, $t$ is the concatenation of some list $u$, then $p$, then some list $v$.
