# Reachability for Boolean PCF with Boolean references is undecidable

Boolean PCF extended with dynamically allocated references holding Booleans has an undecidable reachability problem, because fresh references can simulate generated symbols.

**Theorem.** Extend [Boolean PCF](boolean-pcf-and-its-reachability-problem.md) with a type $\mathbf{bool\ ref}$ and expressions $\mathbf{ref}\ M$ (allocating a new cell initialized with $M : \mathbf{bool}$), $!M$ (dereference, for $M : \mathbf{bool\ ref}$) and $M_1 := M_2$ (assignment, of type $\mathbf{unit}$), with the standard store-based call-by-value reductions. The reachability problem for this language is undecidable.

## Depends on

- [Boolean PCF and its reachability problem](boolean-pcf-and-its-reachability-problem.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Reachability for Boolean PCF with symbol generation is undecidable](reachability-with-symbol-generation-undecidable.md)

## Expansion

The extension with symbol generation translates into this one: $\mathbf{sym}$ becomes $\mathbf{bool\ ref}$, $\mathbf{gensym}()$ becomes $\mathbf{ref}\ \mathbf{true}$, and $x = y$ becomes $x := \mathbf{false};\ y := \mathbf{true};\ !x$. The equality test changes $x$ and then $y$ and checks whether the change to $y$ is visible through $x$, which happens exactly when they are the same cell. The translation preserves reaching $\mathbf{fail}$, so undecidability transfers. Conversely, references can be encoded into symbol generation by a store-passing translation. The source's main positive result identifies a decidable fragment of Boolean PCF with references by a type system, whose well-typed programs translate into pure Boolean PCF; to the source's knowledge, it is the first non-trivial decidable fragment with higher-order recursive functions containing reference cells. A good expansion adds a page that defines Boolean PCF with references and its semantics and a lemma stating that the translation from symbol generation preserves reaching $\mathbf{fail}$ (Section 3.4 of the source).

## Sources

- Naoki Kobayashi, "On Decidable and Undecidable Extensions of Simply Typed Lambda Calculus", *Proceedings of the ACM on Programming Languages* 9(POPL), 2025, pp. 1136–1166, <https://doi.org/10.1145/3704875>; read as arXiv:2411.06086v2, <https://arxiv.org/abs/2411.06086v2>: Theorem 3.3 in Section 3.4 ("Extension with Boolean References") with the translation from symbol generation, and Section 4 ("Decidable References", Corollary 4.2), in the numbering of that version.
