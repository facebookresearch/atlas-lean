# Term rewriting systems

A *term rewriting system* over a signature $\Sigma$ and a set of variables $V$ is a set $R$ of rules $l \to r$ between terms of $T(\Sigma, V)$ such that $l$ is not a variable and every variable of $r$ occurs in $l$. The rewrite relation $\to_R$ is the least relation containing $\sigma(l) \to_R \sigma(r)$ for every rule $l \to r$ and substitution $\sigma$ and closed under contexts: if $s \to_R t$ then $u[s]_p \to_R u[t]_p$ for every term $u$ and position $p$ of $u$.

## Depends on

- [Terms for unification](../first-order-unification/term.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- N-ary ranked-signature adapter for curried unification (proof prerequisite)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, 2019/20, Section 4.2, definitions of rewrite rules, term rewrite systems and the rewrite relation, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>
- F. Baader and T. Nipkow, *Term Rewriting and All That*, Cambridge University Press, 1998
