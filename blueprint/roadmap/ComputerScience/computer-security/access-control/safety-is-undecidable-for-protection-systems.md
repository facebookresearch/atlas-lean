# Safety is undecidable for protection systems

Use the protection systems, configurations and the notion that a configuration is *safe* for a generic right $r$ (no sequence of commands leaks $r$
into a cell of the access matrix that did not previously contain it) from
[protection systems in the access-matrix model](protection-systems-in-the-access-matrix-model.md).

**Theorem (Harrison, Ruzzo and Ullman).** It is undecidable whether a given configuration of a given protection system is safe for a given generic
right.

The proof simulates an arbitrary Turing machine in the access matrix, with one command per move of the machine, so that a designated right is
leaked exactly when the machine halts; deciding safety would therefore decide the halting problem. For mono-operational systems, by contrast, safety is decidable.

## Depends on

- [Protection systems in the access-matrix model](protection-systems-in-the-access-matrix-model.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Sources

- M. A. Harrison, W. L. Ruzzo and J. D. Ullman, "Protection in operating systems", *Communications of the ACM* 19(8):461–471, 1976, copy at <https://www.cs.unibo.it/babaoglu/courses/security/resources/documents/harrison-ruzzo-ullman.pdf>: Section 3 (Theorem 1 for mono-operational systems) and Theorem 2 with its proof.
