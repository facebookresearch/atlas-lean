# Summing out one more variable from a marginal

Let $\alpha$ be a finite type, $P : \alpha^n \to \mathbb{R}$ and $S$ a finite set of nodes, and
write $P(x_S)$ for the sum of $P(y)$ over the configurations $y$ that agree with $x$ on $S$. For
a node $i \notin S$ and every $x' \in \alpha^n$,

$$P(x'_S) = \sum_{a \in \alpha} P\big((x'[i \mapsto a])_{S \cup \{i\}}\big),$$

where $x'[i \mapsto a]$ is $x'$ with value $a$ at node $i$.
