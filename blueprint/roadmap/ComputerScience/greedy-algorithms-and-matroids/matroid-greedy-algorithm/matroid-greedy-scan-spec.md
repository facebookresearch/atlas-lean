# Invariant of the greedy scan

Let $M$ be a matroid on a type $\alpha$, let $O$ be an oracle
that accepts a finite set $A \subseteq \alpha$ exactly when $A$ is independent in $M$, let $S$ be a
finite independent set of $M$ and $L$ a list of elements of $\alpha$, and let $T$ be the set
returned by the greedy scan with oracle $O$ from $S$ over $L$. Then $T$ is independent in $M$, and
for every element $e$ of $L$ with $e \notin T$, the set $T \cup \{e\}$ is not independent in $M$.
