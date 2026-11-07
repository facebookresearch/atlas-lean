# Finset and predicate iterations from the bottom agree

Let $\alpha$ be a type, let $f$ map
finite subsets of $\alpha$ to finite subsets of $\alpha$, and let $F$ map predicates on $\alpha$
to predicates on $\alpha$. For a finite set $Z \subseteq \alpha$ write $P_Z$ for the predicate
$t \mapsto t \in Z$, and suppose that for every finite $Z \subseteq \alpha$ and every
$s \in \alpha$, $s \in f(Z)$ if and only if $F(P_Z)(s)$ holds. Write $f^n$ and $F^n$ for the
$n$-fold iterates and $\bot$ for the predicate that is false everywhere. Then for every
$n \in \mathbb{N}$ and every $s \in \alpha$, $s \in f^n(\emptyset)$ if and only if $F^n(\bot)(s)$
holds.
