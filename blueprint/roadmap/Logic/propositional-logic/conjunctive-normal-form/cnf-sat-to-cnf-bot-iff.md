# Satisfiability of a CNF with falsum false

Let the atoms have a distinguished atom $\bot$
and let $\iota$ be an injective numbering of the atoms by natural numbers. For every proposition
$A$, the CNF consisting of the unit clause with the single negative literal on variable
$\iota(\bot)$ followed by the clauses of the CNF of $A$ (atom $a$ read as variable $\iota(a)$) is
satisfiable if and only if some valuation $v$ of the atoms with $v(\bot)$ false makes $A$ true.
