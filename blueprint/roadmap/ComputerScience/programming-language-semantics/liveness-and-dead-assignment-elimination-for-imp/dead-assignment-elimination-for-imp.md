# Dead-assignment elimination for IMP

Let $L(c, X)$ be the set of [live variables](live-variables-of-an-imp-command.md) before an IMP command $c$ relative to $X$. *Dead-assignment elimination* $\mathrm{bury}(c, X)$ replaces by $\mathtt{skip}$ every assignment whose target is dead after it:

$$
\begin{aligned}
\mathrm{bury}(\mathtt{skip}, X) &= \mathtt{skip},\\
\mathrm{bury}(x := a, X) &= x := a \text{ if } x \in X, \text{ and } \mathtt{skip} \text{ otherwise},\\
\mathrm{bury}(c_1 ; c_2, X) &= \mathrm{bury}(c_1, L(c_2, X)) ; \mathrm{bury}(c_2, X),\\
\mathrm{bury}(\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2, X) &= \mathtt{if}\ b\ \mathtt{then}\ \mathrm{bury}(c_1, X)\ \mathtt{else}\ \mathrm{bury}(c_2, X),\\
\mathrm{bury}(\mathtt{while}\ b\ \mathtt{do}\ c, X) &= \mathtt{while}\ b\ \mathtt{do}\ \mathrm{bury}(c, L(\mathtt{while}\ b\ \mathtt{do}\ c, X)).
\end{aligned}
$$

The result has the shape of the argument, except that $\mathtt{skip}$ may come from an assignment. With the [true liveness](true-liveness-of-an-imp-command.md) $L_t$ in place of $L$ the same equations define $\mathrm{bury}_t$.

## Depends on

- [Live variables of an IMP command](live-variables-of-an-imp-command.md)
- [True liveness of an IMP command](true-liveness-of-an-imp-command.md)

## Sources

- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014; revised version of January 21, 2026, <http://concrete-semantics.org/concrete-semantics.pdf>, Section 10.3.3, the definition of $\mathrm{bury}$ and the inversion properties used in the proof of Lemma 10.20; Section 10.4, the remark that $\mathrm{bury}$ carries over to true liveness.
