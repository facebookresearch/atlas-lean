# Reachability for Boolean PCF with algebraic effects is undecidable

Adding algebraic effect operations on base types and their handlers to Boolean PCF makes reachability of the error command undecidable, with shallow handlers and with deep handlers.

**Theorem.** Extend [Boolean PCF](boolean-pcf-and-its-reachability-problem.md) with algebraic effect operations $\mathsf{op}$, each with a fixed type $b_1 \to b_2$ between base types, expressions $\mathsf{op}(V_1, V_2)$ (perform $\mathsf{op}$ on $V_1 : b_1$ with continuation $V_2 : b_2 \to \tau$) and $\mathbf{with}\ H\ \mathbf{handle}\ M$, where a handler $H = \{\mathbf{return}\ x \mapsto M_0,\ \mathsf{op}_1(x, k) \mapsto M_1, \dots, \mathsf{op}_\ell(x, k) \mapsto M_\ell\}$ covers every operation. A handled value $V$ reduces to $M_0[V/x]$; if $F$ is an evaluation context containing no handler, then $\mathbf{with}\ H\ \mathbf{handle}\ F[\mathsf{op}_i(V_1, V_2)]$ reduces to $M_i[V_1/x,\ \kappa/k]$, where under *deep* handlers $\kappa = \lambda y.\,\mathbf{with}\ H\ \mathbf{handle}\ F[V_2\,y]$ and under *shallow* handlers $\kappa = \lambda y.\,F[V_2\,y]$. For either choice of semantics, the reachability problem for this language is undecidable.

The source credits the original undecidability result to Dal Lago and Ghyselen (POPL 2024).

## Depends on

- [Boolean PCF and its reachability problem](boolean-pcf-and-its-reachability-problem.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Dal Lago and Ghyselen showed that model checking an extension of Boolean PCF with algebraic effects is undecidable by encoding PCF over natural numbers; the source gives a streamlined encoding specialized to Minsky machines. A counter value $n$ is a thunk performing $n$ effects $\mathsf{op}_S$ followed by one $\mathsf{op}_Z$; incrementing wraps the counter in one more $\mathsf{op}_S$. A zero test runs the counter under a handler that jumps to one program point on $\mathsf{op}_Z$ and, on $\mathsf{op}_S$, binds the continuation, which is the predecessor, and jumps to the other. With shallow handlers this works directly. With deep handlers the handler would also catch the later effects, so the encoding uses Dal Lago and Ghyselen's trick of primed copies $\mathsf{op}_{S'}$, $\mathsf{op}_{Z'}$ and wrapping handlers so that only the first effect is interpreted. Halting becomes $\mathbf{fail}$. The restriction of operations to base types matters: with effects on higher-order values exceptions could be encoded directly.

## Sources

- Naoki Kobayashi, "On Decidable and Undecidable Extensions of Simply Typed Lambda Calculus", *Proceedings of the ACM on Programming Languages* 9(POPL), 2025, pp. 1136–1166, <https://doi.org/10.1145/3704875>; read as arXiv:2411.06086v2, <https://arxiv.org/abs/2411.06086v2>: Section 3.2 ("An Extension with Algebraic Effects and Handlers": typing and reduction rules), the encodings of Minsky machines with shallow and with deep handlers in Sections 3.2.1 and 3.2.2, and Remark 3.3, in the numbering of that version; the two undecidability results there are stated without numbers.
