# Three-valued semantics of LTL on finite prefixes

For an LTL formula $\varphi$ and a finite word $u$, define $[u \models_3 \varphi] = \top$ if $uw \models \varphi$ for every infinite word $w$, $[u \models_3 \varphi] = \bot$ if $uw \not\models \varphi$ for every infinite word $w$, and $[u \models_3 \varphi] = {?}$ otherwise. Definite verdicts are stable: if $[u \models_3 \varphi] \in \{\top, \bot\}$ then $[uv \models_3 \varphi] = [u \models_3 \varphi]$ for every finite $v$. The formula $\varphi$ is *monitorable* if every finite word $u$ has an extension $uv$ with a definite verdict.

## Depends on

- [Satisfaction of LTL formulas on ω-words](../../../Logic/temporal-logic/linear-temporal-logic/satisfies.md)

## Sources

- A. Bauer, M. Leucker and C. Schallhart, "Runtime verification for LTL and TLTL", *ACM Transactions on Software Engineering and Methodology* 20(4), Article 14, 2011
