# Gen and kill sets of an IMP command

For an IMP [command](../operational-semantics-of-imp/cmd.md) $c$, the set $\mathit{kill}(c)$ of variables definitely written by $c$ and the set $\mathit{gen}(c)$ of variables that $c$ may read before writing them are defined by recursion on $c$, with $\mathrm{vars}(e)$ the variables of an expression $e$:

$$
\begin{aligned}
\mathit{kill}(\mathtt{skip}) &= \emptyset, & \mathit{gen}(\mathtt{skip}) &= \emptyset,\\
\mathit{kill}(x := a) &= \{x\}, & \mathit{gen}(x := a) &= \mathrm{vars}(a),\\
\mathit{kill}(c_1 ; c_2) &= \mathit{kill}(c_1) \cup \mathit{kill}(c_2), & \mathit{gen}(c_1 ; c_2) &= \mathit{gen}(c_1) \cup (\mathit{gen}(c_2) \setminus \mathit{kill}(c_1)),\\
\mathit{kill}(\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2) &= \mathit{kill}(c_1) \cap \mathit{kill}(c_2), & \mathit{gen}(\mathtt{if}\ b\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2) &= \mathrm{vars}(b) \cup \mathit{gen}(c_1) \cup \mathit{gen}(c_2),\\
\mathit{kill}(\mathtt{while}\ b\ \mathtt{do}\ c) &= \emptyset, & \mathit{gen}(\mathtt{while}\ b\ \mathtt{do}\ c) &= \mathrm{vars}(b) \cup \mathit{gen}(c).
\end{aligned}
$$

A *gen/kill analysis* is a function of the form $A(c, S) = \mathit{gen}(c) \cup (S \setminus \mathit{kill}(c))$.

## Depends on

- [Commands of IMP](../operational-semantics-of-imp/cmd.md)
- [Live variables of an IMP command](live-variables-of-an-imp-command.md)

## Sources

- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014; revised version of January 21, 2026, <http://concrete-semantics.org/concrete-semantics.pdf>, Section 10.3.1, the definitions of $\mathit{kill}$ and $\mathit{gen}$ and of gen/kill analyses.
