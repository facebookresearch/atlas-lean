# Minimal covers and third normal form of 3NF synthesis

[Synthesis](synthesize.md), [Synthesis is lossless](synthesize-lossless.md) and
[Synthesis is dependency-preserving](synthesize-dependency-preserving.md) state the 3NF synthesis algorithm and its
losslessness and dependency preservation for any cover and superkey. This node collects the clauses they do not
state.

## Expansion

A sound expansion has separate pages for:

1. **Minimal covers.** A minimal cover of a set $F$ of functional dependencies is a set $G$ equivalent to $F$ in
   which every right side is a single attribute, no dependency $X \to A$ of $G$ has an extraneous left attribute
   ($F$ derives no $Y \to A$ with $Y \subsetneq X$), and no proper subset of $G$ is equivalent to $F$. Every finite
   $F$ has a minimal cover, computed in polynomial time by splitting right sides, then removing extraneous left
   attributes, then removing redundant dependencies.
2. **Third normal form of the result.** A scheme $S$ is in third normal form for $F$ when every nontrivial
   dependency $X \to A$ derivable from $F$ with $X \cup \{A\} \subseteq S$ has $X$ a superkey of $S$ or $A$ in some
   candidate key of $S$. If $G$ is a minimal cover of $F$ and $K$ is a candidate key of all attributes, every scheme
   synthesized from $G$ and $K$ is in third normal form for $F$. Both hypotheses are needed: for attributes
   $A, B, C$ and $F = \{A \to B\}$, the superkey $ABC$ gives the scheme $ABC$, which violates third normal form, and
   so does the scheme $ABC$ synthesized from the non-minimal cover $\{AC \to B, A \to B\}$.

## Depends on

- [Synthesis](synthesize.md)
- [Equivalent sets of functional dependencies](equivalent.md)
- [Derivability with Armstrong's axioms](../functional-dependencies/derives.md)
- [Superkey](../functional-dependencies/is-superkey.md)
- [Candidate key](../functional-dependencies/is-candidate-key.md)

## Sources

- Foundations of Databases (Abiteboul, Hull, Vianu) — Abiteboul, Hull, Vianu; authors' free web edition (webdam.inria.fr/Alice), Definition 11.2.11 and the definition of a minimal cover (p. 257), Algorithm 11.2.13 and Theorem 11.2.14 (pp. 257–258), and Exercise 11.16 (a polynomial-time minimal-cover algorithm), all.pdf. <http://webdam.inria.fr/Alice/pdfs/all.pdf>
