# $d$-ary sift-down

Let $\alpha$ be a linearly ordered type, let $a$ be an array over
$\alpha$, and let $i$ and $d$ be natural numbers with $d \ge 2$. Sifting down from $i$ in $a$
returns $a$ if $i$ has no valid $d$-ary child in $a$. Otherwise let $c$ be the smallest valid
$d$-ary child of $i$, with ties broken toward the lowest child offset: if $a_c < a_i$, swap the
entries at $i$ and $c$ and sift down from $c$ in the resulting array; otherwise return $a$.
