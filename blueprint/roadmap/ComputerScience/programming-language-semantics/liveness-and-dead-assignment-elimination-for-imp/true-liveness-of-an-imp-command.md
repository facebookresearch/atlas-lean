# True liveness of an IMP command

*True liveness* refines [live variables of an IMP command](live-variables-of-an-imp-command.md) so that the variables read by an assignment to a dead variable are not made live. For a command $c$ and a set $X$ of variables read after $c$, $L_t(c, X)$ is defined by recursion on $c$:

$$
\begin{aligned}
L_t(\mathtt{skip}, X) &= X,\\
L_t(x := a, X) &= \mathrm{vars}(a) \cup (X \setminus \{x\}) \text{ if } x \in X, \text{ and } X \text{ otherwise},\\
L_t(c_1 ; c_2, X) &= L_t(c_1, L_t(c_2, X)),\\
L_t(\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2, X) &= \mathrm{vars}(b) \cup L_t(c_1, X) \cup L_t(c_2, X),\\
L_t(\mathtt{while}\ b\ \mathtt{do}\ c, X) &= \mathrm{lfp}\bigl(Y \mapsto \mathrm{vars}(b) \cup X \cup L_t(c, Y)\bigr),
\end{aligned}
$$

where $\mathrm{lfp}$ is the least fixed point in the complete lattice of sets of variables, ordered by inclusion. The definition is well formed because $L_t(c, \cdot)$ is monotone for every command $c$, by induction on $c$, so the map whose least fixed point is taken in the loop case is monotone. The loop case can no longer be a single union: in $\mathtt{while}\ b\ \mathtt{do}\ c$ a variable may become live only after several iterations of the body. For a finite $X$, the least fixed point is reached by iterating the map from $\emptyset$ until it is stable: the iterates stay inside the finite set of subsets of $X$ and the variables of the command, where the iteration stabilizes, and a stable iterate is the least fixed point.

## Depends on

- [Commands of IMP](../operational-semantics-of-imp/cmd.md)
- [Live variables of an IMP command](live-variables-of-an-imp-command.md)
- [Complete lattice](../../../Order/lattices-boolean-algebras/complete-lattice.md)

## Proof depends on

- [Kleene iteration from the bottom stabilizes on a finite partial order](../dataflow-analysis-by-kleene-iteration/kildall-stabilizes.md)
- [A stable Kleene iterate is the least fixed point](../dataflow-analysis-by-kleene-iteration/kildall-eq-lfp.md)

## Sources

- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014; revised version of January 21, 2026, <http://concrete-semantics.org/concrete-semantics.pdf>, Section 10.4: the redefinition of $L$ with the conditional assignment case and the least fixed point in the loop case, Lemma 10.30 ($L\ c$ is monotone), and Lemmas 10.32 and 10.34 (computing the least fixed point by iteration from $\{\}$ when a finite bound exists).
