# Total-correctness verification conditions are sufficient

If every [total-correctness verification condition](total-correctness-verification-conditions-with-variants.md) of a properly annotated specification $[P]\, C\, [Q]$ is true for every state and auxiliary-variable assignment in the standard integer interpretation specified there, then the unannotated command terminates from every state satisfying $P$ in a state satisfying $Q$.

## Expansion

This page needs a source that proves the statement. Both sources consulted pose it only as an exercise: Gordon leaves the extension of the partial-correctness justification to the reader, and Nipkow and Klein's Exercise 12.21 asks for the soundness proof of a verification-condition generator with measure annotations. A ready expansion fixes one form (integer variants with a nonnegativity condition, or natural-number measure functions), cites a source that proves it, and adds a page for the soundness of the total-correctness while rule in the syntactic setting.

## Depends on

- [Total-correctness verification conditions with variants](total-correctness-verification-conditions-with-variants.md)

## Proof depends on

- [Soundness of Hoare logic over a first-order assertion language](soundness-of-hoare-logic-over-a-first-order-assertion-language.md)
- [Syntactic verification conditions are sufficient](syntactic-verification-conditions-are-sufficient.md)

## Sources

- M. Gordon, *Background reading on Hoare Logic*, University of Cambridge Computer Laboratory, 2016, <https://www.cl.cam.ac.uk/archive/mjcg/HL/Notes/Notes.pdf>: Section 5.6, closing sentence (the justification is left as an exercise); the worked example there has a false condition (iv) when $Y = 0$.
- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014, authors' copy <http://concrete-semantics.in.tum.de/concrete-semantics-brick.pdf>, Section 12.5, Exercise 12.21 (exercise only).
