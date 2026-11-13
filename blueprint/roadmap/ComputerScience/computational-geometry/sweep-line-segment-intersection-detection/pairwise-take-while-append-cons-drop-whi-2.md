# Inserting into a weakly sorted list

Let $f$ map a type $\alpha$ to a linearly ordered
set, let $T$ be a list over $\alpha$ with $f(j) \le f(k)$ whenever $j$ occurs before $k$, let
$i \in \alpha$, and let $P$ be a predicate that holds for an element $j$ of $T$ exactly when
$f(j) < f(i)$. Insert $i$ just before the first element of $T$ not satisfying $P$: the list made
of the longest prefix of $T$ satisfying $P$, then $i$, then the rest of $T$. In this list,
$f(j) \le f(k)$ whenever $j$ occurs before $k$.
