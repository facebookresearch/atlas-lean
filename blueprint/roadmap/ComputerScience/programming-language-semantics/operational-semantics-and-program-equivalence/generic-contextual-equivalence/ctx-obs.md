# Observations over a context algebra

Let $A$ be a [typed context algebra](ctx-algebra.md) with judgments $J$ and term families $\mathrm{Tm}_k$. An observation structure over $A$ consists of:

- a predicate on $J$ marking the program judgments;
- a type of outcomes;
- for each judgment $k$, a type of labels $L_k$;
- for each program judgment $k$, an [operational semantics](../operational-semantics-over-labelled-transition-s/op-sem.md) on $\mathrm{Tm}_k$ with labels $L_k$; and
- for each judgment $k$, a relation $\mathrm{outcome}$ between terms of $\mathrm{Tm}_k$ and outcomes.

The outcome relation is part of the data, independent of the semantics: a program [yields](yields.md) an outcome $o$ when it reaches a final configuration $q$ with $\mathrm{outcome}(q, o)$, so changing only this relation changes which outcomes a final term yields.
