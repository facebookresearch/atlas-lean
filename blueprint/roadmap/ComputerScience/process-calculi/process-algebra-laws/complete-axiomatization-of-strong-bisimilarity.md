# Complete axiomatization of strong bisimilarity for finite CCS

For recursion-free CCS processes, with action prefixing $a.p$, choice $p + q$, the inactive process $\mathbf{0}$, parallel composition, restriction and relabelling, consider the following equational theory:
- associativity, commutativity and idempotence of $+$, with $\mathbf{0}$ as unit: $x + y = y + x$, $(x + y) + z = x + (y + z)$, $x + x = x$, $x + \mathbf{0} = x$;
- the laws distributing restriction and relabelling over $\mathbf{0}$, prefixes and choice;
- the expansion law, which rewrites a parallel composition of two sums of prefixed processes as the sum of their interleavings and synchronizations.

It is sound and ground-complete for strong bisimilarity. Two finite processes, that is, terms without variables, are strongly bisimilar if and only if their equality is derivable in equational logic. Completeness is proved by rewriting every process to a normal form $\sum_{i \in I} a_i . p_i$ and comparing normal forms.

The expansion law is a schema with infinitely many instances, and this is unavoidable. Moller showed that CCS modulo bisimilarity has no finite axiomatization without auxiliary operators. Adding the left merge and communication merge of ACP yields finite axiomatizations.

## Background

- [Choice preserves strong bisimilarity in CCS with communication](../calculus-of-communicating-systems/communication-choice-congr.md)

## Expansion

This page becomes ready once:

- The exact axiom schemas for restriction and relabelling over $\mathbf{0}$, prefixes and choice, and the expansion law for parallel composition, stated as in Milner's table of equational laws (statement prerequisite; not yet stated)

## Sources

- L. Aceto, A. Ingólfsdóttir, B. Luttik and P. van Tilburg, "Finite equational bases for fragments of CCS with restriction and relabelling", *Fifth IFIP International Conference on Theoretical Computer Science (TCS 2008)*, Springer, 2008, <https://luttik.win.tue.nl/Papers/CCSresrel.pdf>, Section 1 (Hennessy and Milner's ground-complete axiomatization of CCS modulo bisimilarity, its necessary infiniteness by Moller's result, and finite axiomatizations with auxiliary operators) and Table 2.2 (the axioms for choice, restriction and relabelling).
