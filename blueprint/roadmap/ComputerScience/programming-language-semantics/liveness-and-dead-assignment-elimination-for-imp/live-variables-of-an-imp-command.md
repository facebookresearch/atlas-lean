# Live variables of an IMP command

For an arithmetic or Boolean expression $e$ of [IMP](../operational-semantics-of-imp/cmd.md), let $\mathrm{vars}(e)$ be the set of variables occurring in $e$. For a [command](../operational-semantics-of-imp/cmd.md) $c$ and a set $X$ of variables, regarded as read after $c$, the set $L(c, X)$ of variables *live before* $c$ relative to $X$ is defined by recursion on $c$:

$$
\begin{aligned}
L(\mathtt{skip}, X) &= X,\\
L(x := a, X) &= \mathrm{vars}(a) \cup (X \setminus \{x\}),\\
L(c_1 ; c_2, X) &= L(c_1, L(c_2, X)),\\
L(\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2, X) &= \mathrm{vars}(b) \cup L(c_1, X) \cup L(c_2, X),\\
L(\mathtt{while}\ b\ \mathtt{do}\ c, X) &= \mathrm{vars}(b) \cup X \cup L(c, X).
\end{aligned}
$$

A variable is *dead* before $c$ relative to $X$ if it is not in $L(c, X)$. The analysis does not evaluate Boolean conditions: a variable live on entry to either branch of a conditional, or read by its condition, is live before it. It is also weaker than the semantic notion of liveness. For example, $y$ is live before $x := y;\ x := 0;\ y := 1$ relative to any $X$, although its initial value cannot affect the final state.

## Depends on

- [Commands of IMP](../operational-semantics-of-imp/cmd.md)

## Sources

- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014; revised version of January 21, 2026, <http://concrete-semantics.org/concrete-semantics.pdf>, Section 10.3: the informal notion of liveness, Example 10.14 (including $x := y;\ x := 0;\ y := 1$), and the recursive definition of $L\ c\ X$.
