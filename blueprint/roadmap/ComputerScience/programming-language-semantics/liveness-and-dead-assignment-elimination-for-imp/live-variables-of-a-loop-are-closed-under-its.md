# Live variables of a loop are closed under its body

Let $w = \mathtt{while}\ b\ \mathtt{do}\ c$ be an IMP command and $X$ a set of variables. Then the [live variables](live-variables-of-an-imp-command.md) satisfy $L(c, L(w, X)) \subseteq L(w, X)$. Moreover $L(w, X)$ is the least set $P$ with $\mathrm{vars}(b) \subseteq P$, $X \subseteq P$ and $L(c, P) \subseteq P$.

**Proof.** By [the gen/kill form](liveness-is-a-gen-kill-analysis.md), $\mathit{gen}(c) \subseteq \mathit{gen}(w) \subseteq L(w, X)$, so $L(c, L(w, X)) = \mathit{gen}(c) \cup (L(w, X) \setminus \mathit{kill}(c)) \subseteq L(w, X)$. If $P$ satisfies the three constraints, then $\mathit{gen}(c) \subseteq L(c, P) \subseteq P$, so $L(w, X) = \mathrm{vars}(b) \cup \mathit{gen}(c) \cup X \subseteq P$.

## Depends on

- [Live variables of an IMP command](live-variables-of-an-imp-command.md)

## Proof depends on

- [Liveness is a gen/kill analysis](liveness-is-a-gen-kill-analysis.md)

## Sources

- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014; revised version of January 21, 2026, <http://concrete-semantics.org/concrete-semantics.pdf>, Section 10.3.1: the constraint system (10.1), Lemma 10.16 with its proof, and the proof that $L\ w\ X$ is the least solution of (10.1).
