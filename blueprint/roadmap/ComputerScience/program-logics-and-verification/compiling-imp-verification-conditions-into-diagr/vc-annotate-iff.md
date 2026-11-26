# Diagram obligations of the compiled annotation and IMP verification conditions

For an annotated IMP command $c$ and assertions $P$ and $Q$, consider the [compiled annotation](annotate.md) $\mathrm{annotate}(c, Q)$ of the compiled diagram of $c$. Its diagram obligations from the set of $P$-states to the set of $Q$-states hold if and only if $P$ entails the [generated precondition](../verification-condition-generation/pre.md) $\mathrm{pre}(c, Q)$ and the [verification conditions](../verification-condition-generation/vc.md) $\mathrm{vc}(c, Q)$ hold.

The statement concerns this particular annotation. Another annotation of the same diagram can fail even when the source conditions hold: for $\mathtt{skip}; \mathtt{skip}$ with $P = Q = \mathrm{True}$, an annotation that places $\mathrm{False}$ on the middle wire has a failing obligation.
