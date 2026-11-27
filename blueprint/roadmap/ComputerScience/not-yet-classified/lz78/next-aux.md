# Next LZ78 phrase

For a list of phrases $D$, a phrase $c$ and a finite list $x$, write
`ι v` for `([] :: D).idxOf v`, the first position of $v$ in the list $D$ with the empty phrase in
front (its length $|D| + 1$ when $v$ does not occur). If $x$ is empty, the result is the phrase
$c$, the token `(ι c, none)` and the empty list. If $x$ is a symbol $a$ followed by a list $x'$,
the result is that for the phrase `c ++ [a]` and $x'$ when `c ++ [a]` is an entry of $D$, and
otherwise the phrase `c ++ [a]`, the token `(ι c, some a)` and $x'$.
