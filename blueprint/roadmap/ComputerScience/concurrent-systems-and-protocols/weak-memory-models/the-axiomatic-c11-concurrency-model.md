# The axiomatic C11 concurrency model

In the axiomatic C11 memory model, a candidate execution of a program consists of its memory actions with the sequenced-before relation, together with a reads-from relation, a modification order (a total order on the writes to each atomic location) and a total order on sequentially consistent actions; happens-before is derived from sequenced-before and synchronizes-with. An execution is consistent if it satisfies the model's consistency axioms (coherence, visibility of reads, atomicity of read-modify-writes and the SC axioms). A program whose consistent executions include one with a data race on a non-atomic location, two conflicting accesses unordered by happens-before, has undefined behavior.

## Expansion

This page becomes ready once:

- Consistency axioms of a fixed formalization of the C11 model, as in Batty, Owens, Sarkar, Sewell and Weber (statement prerequisite; not yet stated)

## Sources

- M. Batty, S. Owens, S. Sarkar, P. Sewell and T. Weber, "Mathematizing C++ concurrency", *Proceedings of the 38th ACM POPL*, 2011
