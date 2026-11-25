# Hoare triples as KAT absorption equations

Fix a PDL model $M$ with worlds $W$, write $R_a \subseteq W \times W$ for the relation of a
program $a$ (the pairs $(s, t)$ such that $a$ can run from $s$ to $t$), $P?$ for the identity
relation on a set $P \subseteq W$, and $R ; S$ for the composite of relations (first $R$, then $S$).

The Hoare triple $\{P\}\, a\, \{Q\}$ holds if and only if $P? ; R_a = P? ; R_a ; Q?$, the
absorption form of partial correctness in Kleene algebra with tests.
