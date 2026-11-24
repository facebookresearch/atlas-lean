# Type safety of let-polymorphism

Consider core ML: variables, constants, abstraction $\lambda z.\, t$, application and $\mathbf{let}\ z = t_1\ \mathbf{in}\ t_2$, with a call-by-value
small-step semantics, typed by the Damas–Milner system with let-generalization. An initial environment $\Gamma_0$ assigns closed type
schemes to the constants and must agree with their reduction rules $\xrightarrow{\delta}$:

1. each $\delta$-reduction preserves typing, and
2. every well-typed application $c\, v_1 \cdots v_k$ of a constant to values is either reducible or a value.

If all constants are pure, or every program satisfies the *value restriction* (each $\mathbf{let}\ z = t_1\ \mathbf{in}\ t_2$ has $t_1$ a value), then:

- **Subject reduction.** Reduction preserves well-typedness: a well-typed program reduces only to a well-typed program at the same type.
- **Progress.** A well-typed program is either reducible or a value.
- **Type soundness.** Well-typed programs do not go wrong: no well-typed program reduces to a stuck configuration.

Both properties hold with well-typedness defined by the Damas–Milner typing judgment. With mutable references the value restriction is
needed: without it, $\mathbf{let}\ r = \mathrm{ref}\,(\lambda z.\, z)$ receives the scheme $\forall X.\, \mathrm{ref}\,(X \to X)$, and a program can store an integer
function in $r$ and read it back at type $\mathrm{bool} \to \mathrm{bool}$.

## Depends on

- [Hindley–Milner typing](../hindley-milner-type-inference/has-type.md)

## Proof depends on

- [Syntactic type soundness](syntactic-type-soundness.md)

## Sources

- F. Pottier and D. Rémy, "The essence of ML type inference", in B. C. Pierce (ed.), *Advanced Topics in Types and Programming Languages*, MIT Press, 2005, Chapter 10, <http://gallium.inria.fr/~fpottier/publis/emlti-final.pdf>: Section 10.5 (Definitions 10.5.2, 10.5.5 and 10.5.6, the value-restriction example, Theorems 10.5.8, 10.5.10 and 10.5.11, and the remark that soundness transfers to Damas–Milner typing by Theorems 10.3.6 and 10.4.8).
- R. Milner, "A theory of type polymorphism in programming", *Journal of Computer and System Sciences* 17(3):348–375, 1978 (not opened; the slogan and its role are as reported by Pottier and Rémy, Section 10.5).
