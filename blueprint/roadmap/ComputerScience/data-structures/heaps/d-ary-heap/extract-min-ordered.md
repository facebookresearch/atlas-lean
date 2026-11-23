# Extracting the minimum leaves a heap-ordered $d$-ary heap

Let $h$ be a $d$-ary
min-heap. If extracting the minimum of $h$ returns a value $x$ and a heap $h'$ of arity $d'$,
then $d' \ge 2$ and the storage array $a$ of $h'$ is heap-ordered: for every index $i$ with
$0 < i < |a|$, the entry $a_{\lfloor (i-1)/d' \rfloor}$ is at most $a_i$.
