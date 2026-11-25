# Valiant's elimination algorithm for k-CNF

Given a list of positive examples (truth assignments at which the target is true), the elimination
algorithm starts from all clauses of at most $k$ literals and deletes each clause falsified by some
example; it outputs the conjunction of the remaining clauses. Valiant's loop body is "for each
$c_i$ in $g$ delete $c_i$ if $v \not\Rightarrow c_i$", repeated over the examples $v$; the result
does not depend on the order of the examples.

Valiant works with partial vectors (some variables undetermined); here examples are total
assignments.

## Sources

- L. G. Valiant, *A theory of the learnable*, Communications of the ACM 27 (1984), 1134-1142, Section 5, proof of Theorem A.
