# Type safety of let-polymorphism

Consider core ML: variables, constants, abstraction $\lambda z.\, t$, application and $\mathbf{let}\ z = t_1\ \mathbf{in}\ t_2$, with a call-by-value
small-step semantics, typed by the Damas–Milner system with let-generalization. A signature has finitely many constants: an initial environment
$\Gamma_0$, a list whose visible type schemes are closed, binds each constant to its type scheme, and each constant has an arity and is a
constructor or a destructor. The reduction rules $\xrightarrow{\delta}$ of the constants are pure, that is, they neither read nor update a store,
and they agree with the signature:

1. each $\delta$-redex is a destructor applied to exactly as many values as its arity, and the $\delta$-reduct of a redex that binds no constant binds no constant;
2. each $\delta$-reduction of a redex that binds no constant preserves typing in $\Gamma_0$; and
3. every well-typed application $c\, v_1 \cdots v_k$ of a constant to values that binds no constant is either reducible or a value.

Programs never bind a constant, since program variables and constants are distinct, so these conditions say nothing about an expression that does.

**Type soundness.** Let a program bind no constant and have a type in $\Gamma_0$. Then no configuration it reduces to is stuck: every program it
reduces to in finitely many steps is a value or is reducible. The result follows from
[subject reduction](../hindley-milner-type-inference/preservation.md) and [progress](../hindley-milner-type-inference/progress.md).

Mutable references are outside this statement: their soundness needs a store typing, preservation up to an extension of the store typing, and the
*value restriction* (each $\mathbf{let}\ z = t_1\ \mathbf{in}\ t_2$ has $t_1$ a value). Without the restriction,
$\mathbf{let}\ r = \mathrm{ref}\,(\lambda z.\, z)$ receives the scheme $\forall X.\, \mathrm{ref}\,(X \to X)$, and a program can store an integer
function in $r$ and read it back at type $\mathrm{bool} \to \mathrm{bool}$.

## Sources


- F. Pottier and D. Rémy, "The essence of ML type inference", in B. C. Pierce (ed.), *Advanced Topics in Types and Programming Languages*, MIT Press, 2005, Chapter 10, <http://gallium.inria.fr/~fpottier/publis/emlti-final.pdf>: Section 10.5 (Definitions 10.5.2, 10.5.5 and 10.5.6, the value-restriction example, Theorems 10.5.8, 10.5.10 and 10.5.11, and the remark that soundness transfers to Damas–Milner typing by Theorems 10.3.6 and 10.4.8).
