# Sierpiński's theorem on atomless measures

Let $\mu$ be a finite atomless measure: every measurable set $s$ with $\mu(s) > 0$ contains a
measurable subset $t$ with $0 < \mu(t) < \mu(s)$. Then for every measurable set $s$ and every $t$
with $0 \le t \le \mu(s)$ there is a measurable set $u \subseteq s$ with $\mu(u) = t$.

## Idea

Being atomless only says that every set of positive measure can be split somewhere. Sierpiński's
theorem says much more: every intermediate value is attained, as for Lebesgue measure on
$[0, 1]$, where $[0, t]$ has measure $t$. The proof first splits repeatedly to find subsets of
arbitrarily small positive measure, then exhausts: at each step it adds a piece whose measure is at
least half the supremum of what can still be added without overshooting $t$. The increasing union
of these pieces has measure exactly $t$, since otherwise a further small piece could still be
added. The other statements are basic facts of the definition.

## Statements

- [Sierpiński's theorem on atomless measures](is-atomless-exists-subset-measure-eq.md)
- [Atomless measure](is-atomless.md): the definition.
- [Atomless measures have null singletons](null-singleton-class.md): a basic fact of the definition.
- [Restriction of an atomless measure](is-atomless-restrict.md): a basic fact of the definition.
