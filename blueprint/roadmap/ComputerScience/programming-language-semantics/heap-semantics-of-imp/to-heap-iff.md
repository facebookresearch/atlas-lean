# Heap steps of embedded commands are plain steps

Let $c$ be a plain IMP command, $s$ a
store and $h$ a heap, and write $\overline{d}$ for the embedding of a plain command $d$ into the
heap language. Then $(\overline{c}, s, h)$ takes a heap step to a heap configuration $K$ if and
only if there are a plain command $c'$ and a store $s'$ such that $(c, s)$ takes a plain small
step to $(c', s')$ and $K = (\overline{c'}, s', h)$.
