# Loop exit absorption from a guarded-body absorption equation

Fix a PDL model $M$ with worlds $W$, write $R_a \subseteq W \times W$ for the relation of a
program $a$ (the pairs $(s, t)$ such that $a$ can run from $s$ to $t$), $P?$ for the identity
relation on a set $P \subseteq W$, and $R ; S$ for the composite of relations (first $R$, then $S$).

Let $g$ be a formula, $G$ the set of worlds where it holds, and $w$ the loop
$\mathbf{while}\ g\ \mathbf{do}\ a$. If $(I \cap G)? ; R_a = (I \cap G)? ; R_a ; I?$, then
$I? ; R_w = I? ; R_w ; (I \setminus G)?$: the absorption form of the while rule.
