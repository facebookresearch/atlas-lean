# Equational consequence and E-algebras

Let $E$ be a set of equations $s \approx t$ between [terms](../first-order-unification/unification-of-ranked-terms-through-the-curried-encoding.md) of $T_\Sigma(X)$, for a countably infinite set $X$ of variables, so that $T_\Sigma(X)$ is nonempty, each read as its universal closure $\forall \vec x\,(s \approx t)$. A $\Sigma$-algebra that is a model of every equation of $E$ is an *$E$-algebra*. For terms $s, t$, write $s \approx_E t$ if $\forall \vec x\,(s \approx t)$ holds in every $E$-algebra; the relation $\approx_E$ is the *equational theory* of $E$.

The *rewrite relation* $\to_E$ of $E$ is defined by $s \to_E t$ if there are an equation $(l \approx r) \in E$, a position $p$ of $s$ and a substitution $\sigma$ with $s|_p = l\sigma$ and $t = s[r\sigma]_p$, as for [term rewriting systems](../automated-deduction/term-rewriting-systems.md) but without restrictions on $l$ and $r$. The closures $\leftrightarrow_E$ and $\leftrightarrow_E^*$ are those of the [abstract reduction system](../term-rewriting/abstract-reduction-system.md) $(T_\Sigma(X), \to_E)$. A set of equations is called terminating, confluent or convergent if $\to_E$ is.

## Depends on

- [Term rewriting systems](../automated-deduction/term-rewriting-systems.md)
- [Unification of ranked terms through the curried encoding](../first-order-unification/unification-of-ranked-terms-through-the-curried-encoding.md)
- [Abstract reduction system](../term-rewriting/abstract-reduction-system.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.2, pp. 106–107: the rewrite relation $\to_E$, E-algebras and the notation $s \approx_E t$.
