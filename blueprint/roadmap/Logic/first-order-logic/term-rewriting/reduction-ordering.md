# Reduction ordering

Let $T_\Sigma(X)$ be the set of [terms](../first-order-unification/unification-of-ranked-terms-through-the-curried-encoding.md) over a signature $\Sigma$ and a set $X$ of variables, with positions, subterms $t|_p$, replacement $t[s]_p$ and substitutions as for [term rewriting systems](../automated-deduction/term-rewriting-systems.md). A binary relation $\sqsupset$ on $T_\Sigma(X)$ is

- *compatible with $\Sigma$-operations* if $s \sqsupset s'$ implies $f(t_1, \dots, s, \dots, t_n) \sqsupset f(t_1, \dots, s', \dots, t_n)$ for all function symbols $f$ and terms $s, s', t_i$; equivalently, $s \sqsupset s'$ implies $t[s]_p \sqsupset t[s']_p$ for every term $t$ and position $p$ of $t$;
- *stable under substitutions* if $s \sqsupset s'$ implies $s\sigma \sqsupset s'\sigma$ for every substitution $\sigma$;
- a *rewrite relation* if it is compatible with $\Sigma$-operations and stable under substitutions.

A *rewrite ordering* is a strict partial ordering on $T_\Sigma(X)$ that is a rewrite relation, and a *reduction ordering* is a rewrite ordering that is well-founded. For every term rewriting system $R$ the rewrite relation $\to_R$ is a rewrite relation.

## Depends on

- [Term rewriting systems](../automated-deduction/term-rewriting-systems.md)
- [Unification of ranked terms through the curried encoding](../first-order-unification/unification-of-ranked-terms-through-the-curried-encoding.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, pp. 114–115: compatibility with $\Sigma$-operations, Lemma 4.18, stability under substitutions, rewrite relations, rewrite orderings and reduction orderings.
