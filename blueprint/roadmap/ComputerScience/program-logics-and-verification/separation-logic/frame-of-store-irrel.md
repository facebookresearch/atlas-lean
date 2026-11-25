# Store-irrelevant frames satisfy the frame-rule side condition

Let $R$ be a
store-irrelevant heap assertion and $c$ a heap command. For all stores $s, s'$ and every heap
$h$, if $R(s, h)$ holds and $s'(x) = s(x)$ for every variable $x$ outside the set of variables
that $c$ may assign to, then $R(s', h)$ holds.

This is the side condition on the frame in the frame rule.
