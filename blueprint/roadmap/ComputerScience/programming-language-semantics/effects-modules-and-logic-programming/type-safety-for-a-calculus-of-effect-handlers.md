# Type safety for a calculus of effect handlers

Consider a fine-grain call-by-value calculus with effect operations $\mathrm{op}$, deep handlers $\{\mathbf{return}\ x \mapsto c_r;\ \mathrm{op}(x; k) \mapsto c_{\mathrm{op}}\}$ and computation types annotated with effect rows, with a small-step semantics in which an operation call is handled by the nearest enclosing handler for it, binding $k$ to the delimited continuation re-wrapped in the handler. Well-typed computations satisfy preservation, and progress: a closed well-typed computation with the empty effect row is either $\mathbf{return}\ v$ or takes a step.

## Expansion

This page becomes ready once:

- Syntactic type safety (proof prerequisite; not yet stated)
- Typing and reduction rules of a fine-grain call-by-value calculus with deep handlers and effect rows (statement prerequisite; not yet stated)

## Sources

- G. Plotkin and M. Pretnar, "Handlers of algebraic effects", *ESOP 2009*, LNCS 5502, Springer, 2009
- A. Bauer and M. Pretnar, "An effect system for algebraic effects and handlers", *Logical Methods in Computer Science* 10(4), 2014
