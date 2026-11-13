# Optimality of the matroid greedy algorithm

Let $M$ be a matroid on a type $\alpha$, let $O$
be an oracle that accepts a finite set $A \subseteq \alpha$ exactly when $A$ is independent in $M$,
and let $w : \alpha \to \mathbb{N}$ be a weight function. Let $L$ be a list of elements of $\alpha$
in nonincreasing order of weight (whenever $a$ occurs before $b$ in $L$, $w(b) \le w(a)$), and let
$G$ be the set returned by the greedy algorithm with oracle $O$ on $L$. Then every finite
independent set $I$ of $M$ whose elements all occur in $L$ satisfies
$\sum_{x \in I} w(x) \le \sum_{x \in G} w(x)$.

## Sources

- CLRS, third edition, Theorem 16.11.
