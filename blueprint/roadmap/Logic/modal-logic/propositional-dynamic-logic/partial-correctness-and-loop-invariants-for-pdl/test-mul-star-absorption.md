# Test absorption lifts through iteration

Fix a PDL model $M$ with worlds $W$, write $R_a \subseteq W \times W$ for the relation of a
program $a$ (the pairs $(s, t)$ such that $a$ can run from $s$ to $t$), $P?$ for the identity
relation on a set $P \subseteq W$, and $R ; S$ for the composite of relations (first $R$, then $S$).

If $I? ; R_a = I? ; R_a ; I?$, then $I? ; R_{a^*} = I? ; R_{a^*} ; I?$: the absorption form of the
invariant rule for iteration.
