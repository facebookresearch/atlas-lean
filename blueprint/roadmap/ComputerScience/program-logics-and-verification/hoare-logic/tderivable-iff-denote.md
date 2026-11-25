# Total-correctness Hoare logic is sound and complete for the denotational semantics

For
all assertions $P$, $Q$ (predicates on states) and every IMP command $c$, the triple
$\{P\}\,c\,\{Q\}$ is derivable in the total-correctness Hoare logic if and only if for every
state $s$ satisfying $P$ there is a state $s'$ such that $(s, s')$ lies in the relational
denotation of $c$ and $s'$ satisfies $Q$.
