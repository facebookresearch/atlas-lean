# Adequacy of Iris weakest preconditions

Let $\varphi$ be a first-order predicate on values. If the Iris proposition $\mathrm{True} \vdash \mathrm{wp}\ e\ \{\varphi\}$ is derivable and the thread-pool semantics reduces $(e, \sigma) \to^\ast_{tp} (e_1 \dots e_n, \sigma')$, then

1. every thread $e_i$, $1 \le i \le n$, is a value or can reduce in $\sigma'$: $\mathrm{red}(e_i, \sigma')$;
2. if the main thread $e_1$ is a value $v$, then $\varphi(v)$.

So derivable weakest preconditions guarantee safety (no thread gets stuck) and the postcondition of the main thread.

## Expansion

This page becomes ready once these prerequisites are stated:

- The Iris base logic over a camera of resources, with the update and later modalities (statement prerequisite)
- The language interface with thread-pool reduction and the definition of weakest preconditions (statement prerequisite)

## Depends on

- [Resource algebras](resource-algebras.md)

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151>, Section 6.4, Theorem 6, and Section 7, Theorem 7 (a variant for the full program logic, with a state interpretation under the update modality).
