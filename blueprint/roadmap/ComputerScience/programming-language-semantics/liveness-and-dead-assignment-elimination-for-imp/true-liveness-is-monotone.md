# True liveness is monotone

For every IMP command $c$, the map $X \mapsto L_t(c, X)$ of [true liveness](true-liveness-of-an-imp-command.md) is monotone: $X \subseteq Y$ implies $L_t(c, X) \subseteq L_t(c, Y)$.

**Proof.** Induction on $c$, using that union is monotone in both arguments and set difference in the first. In the loop case, the least fixed point is monotone in the function: if $f(A) \subseteq g(A)$ for all $A$, then every pre-fixed point of $g$ is a pre-fixed point of $f$, so $\mathrm{lfp}(f) \subseteq \mathrm{lfp}(g)$.

## Depends on

- [True liveness of an IMP command](true-liveness-of-an-imp-command.md)

## Sources

- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014; revised version of January 21, 2026, <http://concrete-semantics.org/concrete-semantics.pdf>, Section 10.4, Lemma 10.30 with its proof, and the corollary that $\lambda Y.\ \mathrm{vars}\ b \cup X \cup L\ c\ Y$ is monotone.
