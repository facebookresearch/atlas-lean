# Soundness of Hoare logic for partial correctness

Every partial-correctness Hoare triple
$\{P\}\,c\,\{Q\}$ that is derivable in the partial-correctness proof system is valid: for all
states $s$ and $s'$, if $s$ satisfies $P$ and $c$ has a terminating big-step execution from $s$ to
$s'$, then $s'$ satisfies $Q$.
