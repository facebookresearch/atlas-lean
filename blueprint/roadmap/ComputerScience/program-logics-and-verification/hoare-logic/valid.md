# Validity of a Hoare triple

For assertions $P$ and $Q$ and a command $c$, the
partial-correctness Hoare triple $\lbrace P \rbrace\ c\ \lbrace Q \rbrace$ is valid when, for all
states $s$ and $t$, if $s$ satisfies $P$ and executing $c$ from $s$ terminates in $t$ under the
big-step semantics, then $t$ satisfies $Q$.
