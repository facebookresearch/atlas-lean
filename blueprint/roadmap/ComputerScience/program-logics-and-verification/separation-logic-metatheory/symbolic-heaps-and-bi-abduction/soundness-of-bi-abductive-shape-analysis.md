# Soundness of bi-abductive shape analysis

This node covers the soundness of the compositional shape analysis of Calcagno, Distefano, O'Hearn and Yang, which infers procedure specifications by symbolic execution with [bi-abduction](bi-abduction.md), abstraction to list-segment symbolic heaps, and a final re-execution that discards preconditions it cannot verify. Their soundness theorem states that if the specification inference terminates from the seed precondition fixing the initial values of the program's free variables, the inferred specifications over-approximate the concrete meaning of the program, defined from the greatest state transformers satisfying the Hoare triples of its edges, in the style of abstract interpretation, and that every inferred triple is valid.

## Expansion

A good expansion states, on pages of their own: programs as control-flow graphs with procedure summaries; the concrete semantics given by greatest local actions; the abstract domain of symbolic heaps and the precondition-generation and pre/post-synthesis algorithms; and the soundness theorem itself, with both of its formulations checked against the source.

## Depends on

- [Bi-abduction](bi-abduction.md)

## Sources

- C. Calcagno, D. Distefano, P. W. O'Hearn and H. Yang, "Compositional shape analysis by means of bi-abduction", *Journal of the ACM* 58(6), 2011; accepted version (May 2011) <https://www.cs.ox.ac.uk/files/4078/jacm11-biabduction-submitted.pdf>, Section 4, Definition 4.1 and Theorem 4.14.
