# Melding binomial forests

Over a linear order, the meld of two lists of binomial trees
is defined by recursion on their total length. For every list $L$, the meld of the empty list
with $L$ is $L$, and the meld of $L$ with the empty list is $L$. For nonempty lists with first
trees $s$ and $t$ and remaining lists $F$ and $G$: if the rank of $s$ is less than the rank of
$t$, the meld is $s$ followed by the meld of $F$ with the second list; if the rank of $t$ is less
than the rank of $s$, it is $t$ followed by the meld of the first list with $G$; and if the ranks
are equal, it is the result of carrying the link of $s$ with $t$ into the meld of $F$ and $G$.

It is intended for forests of strictly increasing ranks, where equal-rank trees are linked and
the carries are propagated.
