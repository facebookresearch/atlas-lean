# Liveness is a gen/kill analysis

For every IMP command $c$ and set $X$ of variables, the [live variables](live-variables-of-an-imp-command.md) satisfy

$$L(c, X) = \mathit{gen}(c) \cup (X \setminus \mathit{kill}(c)),$$

with the [gen and kill sets](gen-and-kill-sets-of-an-imp-command.md) of $c$.

**Proof.** Induction on $c$.

## Depends on

- [Live variables of an IMP command](live-variables-of-an-imp-command.md)
- [Gen and kill sets of an IMP command](gen-and-kill-sets-of-an-imp-command.md)

## Sources

- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014; revised version of January 21, 2026, <http://concrete-semantics.org/concrete-semantics.pdf>, Section 10.3.1, Lemma 10.15 (liveness via gen/kill).
