# The empty open-addressing table is valid

For all types $K$ and $V$, every number of
slots $m$ and every probe sequence $p$, which assigns to each key $k$ and each $i \in \mathbb{N}$
a slot $p(k, i) \in \{0, \dots, m - 1\}$, the empty table with $m$ slots and probe sequence $p$,
in which every slot is vacant, is valid: it is probe-closed and no key is stored in two
different slots.
