# Threshold counts of the matroid greedy result

Let $M$ be a matroid on a type $\alpha$, let
$O$ be an oracle that accepts a finite set $A \subseteq \alpha$ exactly when $A$ is independent in
$M$, and let $w : \alpha \to \mathbb{N}$ be a weight function. Let $L$ be a list of elements of
$\alpha$ in nonincreasing order of weight (whenever $a$ occurs before $b$ in $L$, $w(b) \le w(a)$),
and let $G$ be the set returned by the greedy algorithm with oracle $O$ on $L$. Then for every
finite independent set $I$ of $M$ whose elements all occur in $L$ and every $t \in \mathbb{N}$, the
number of $x \in I$ with $w(x) > t$ is at most the number of $x \in G$ with $w(x) > t$.
