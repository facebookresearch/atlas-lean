# Insertion into a $d$-ary heap

Inserting a value $x$ into a $d$-ary min-heap $h$ of arity
$d$ gives the heap of the same arity $d$ whose array is obtained by appending $x$ at the end of
the level-order array of $h$ and sifting it up from that last index: while the current index
$i > 0$ holds an entry strictly smaller than the entry at its parent index
$\lfloor (i-1)/d \rfloor$, the two entries are swapped and the process continues from the
parent. Only the ancestor path of the new entry is changed.
