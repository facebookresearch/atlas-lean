# LZ78 decoding from a dictionary

For a list of phrases $D$ and a list of tokens, the
result is `some []` when there are no tokens. For a token `(i, s)` followed by tokens $T$, it is
`none` when $i > |D|$ (a dangling index). Otherwise, with $p$ the entry at position $i$ of the
list $D$ with the empty phrase in front and $w$ the phrase `p ++ s.toList` ($p$ followed by the
symbol of $s$, if any), it is `none` when decoding $T$ from the list `D ++ [w]` fails, and that
result with $w$ in front otherwise.
