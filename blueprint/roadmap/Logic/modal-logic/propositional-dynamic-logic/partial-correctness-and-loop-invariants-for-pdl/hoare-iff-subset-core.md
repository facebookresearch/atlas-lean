# Partial correctness as inclusion in the relational core

Fix a PDL model $M$ with worlds $W$, write $R_a \subseteq W \times W$ for the relation of a
program $a$ (the pairs $(s, t)$ such that $a$ can run from $s$ to $t$), $P?$ for the identity
relation on a set $P \subseteq W$, and $R ; S$ for the composite of relations (first $R$, then $S$).

The Hoare triple $\{P\}\, a\, \{Q\}$ holds if and only if $P$ is contained in the set
$\{s \mid t \in Q \text{ for every } t \text{ with } (s, t) \in R_a\}$ of worlds all of whose
$a$-successors lie in $Q$.
