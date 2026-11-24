# Sift-up

Given an array $a$ of length $|a|$ over a linearly ordered type, indexed from $0$,
and an index $i$, the sift-up of $a$ from $i$ is defined by recursion on $i$. If $i = 0$ or
$i \ge |a|$, the result is $a$. Otherwise let $p = \lfloor (i - 1)/2 \rfloor$ be the parent of
$i$; if $a_i < a_p$, the result is the sift-up from $p$ of the array obtained from $a$ by
exchanging the entries at positions $i$ and $p$, and otherwise the result is $a$.
