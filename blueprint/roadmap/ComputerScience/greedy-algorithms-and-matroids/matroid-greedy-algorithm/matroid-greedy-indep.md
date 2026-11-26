# The matroid greedy result is independent

Let $M$ be a matroid on a type $\alpha$ and let
$O$ be an oracle that accepts a finite set $A \subseteq \alpha$ exactly when $A$ is independent in
$M$. For every list $L$ of elements of $\alpha$, the set returned by the greedy algorithm with
oracle $O$ on $L$ is independent in $M$, and each of its elements occurs in $L$.
