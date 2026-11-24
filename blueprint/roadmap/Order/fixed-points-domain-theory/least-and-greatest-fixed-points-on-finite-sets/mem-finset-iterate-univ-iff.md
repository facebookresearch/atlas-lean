# Finset and predicate iterations from the top agree

Let $\alpha$ be a finite type, let $f$
map subsets of $\alpha$ to subsets of $\alpha$, and let $F$ map predicates on $\alpha$ to
predicates on $\alpha$. For $Z \subseteq \alpha$ write $P_Z$ for the predicate
$t \mapsto t \in Z$, and suppose that for every $Z \subseteq \alpha$ and every $s \in \alpha$,
$s \in f(Z)$ if and only if $F(P_Z)(s)$ holds. Write $f^n$ and $F^n$ for the $n$-fold iterates
and $\top$ for the predicate that is true everywhere. Then for every $n \in \mathbb{N}$ and every
$s \in \alpha$, $s \in f^n(\alpha)$ if and only if $F^n(\top)(s)$ holds.
