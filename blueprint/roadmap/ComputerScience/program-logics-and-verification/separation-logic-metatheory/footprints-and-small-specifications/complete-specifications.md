# Complete specifications of local functions

A specification of a local function is a set of pre/postcondition pairs; it is complete when the triples the function satisfies are exactly those that follow semantically from it. A specification is complete for exactly one local function, its best local function, and every local function has a complete specification on all its safe states.

Let $(\Sigma, \bullet, u)$ be a separation algebra, with local functions, statements, specifications, domains, satisfaction $f \models (p, q)$ and semantic consequence $\varphi \models (p, q)$ as in [soundness of consequence between specifications](soundness-of-consequence-between-specifications.md). The specification $\varphi$ is *complete* for $f$ if, for all predicates $p, q$,

$$f \models (p, q) \iff \varphi \models (p, q).$$

The *best local function* of $\varphi$ is

$$\mathrm{bla}[\varphi]\!(\sigma) = \bigsqcap \{\{\sigma'\} \ast q : \sigma = \sigma' \bullet \sigma'',\ \sigma'' \in p,\ (p, q) \in \varphi\},$$

the meet taken in $P(\Sigma)^\top$, so equal to $\top$ when no statement applies; it is local, satisfies $\varphi$, and lies above every local function satisfying $\varphi$, generalizing the [best local action](../abstract-separation-logic/best-local-action.md) of one pair. Then

1. $\varphi$ is complete for a local function $f$ if and only if $f = \mathrm{bla}[\varphi]$;
2. the canonicalization $\varphi_{\mathrm{can}} = \{(\{\sigma\}, \mathrm{bla}[\varphi]\!(\sigma)) : \sigma \in D(\varphi)\}$ is semantically equivalent to $\varphi$, and complete specifications of $f$ with the same domain have the same canonicalization;
3. the *big specification* $\{(\{\sigma\}, f(\sigma)) : f(\sigma) \neq \top\}$ is complete for $f$ and has the largest domain among complete specifications.

A complete specification of $f$ is *small* if no complete specification of $f$ has a strictly smaller domain.

## Depends on

- [Soundness of consequence between specifications](soundness-of-consequence-between-specifications.md)
- [Local actions](../abstract-separation-logic/local-actions.md)
- [The best local action of a specification](../abstract-separation-logic/best-local-action.md)

## Proof depends on

- [The best local action of a specification](../abstract-separation-logic/best-local-action.md)
- [Soundness of consequence between specifications](soundness-of-consequence-between-specifications.md)

## Expansion

For part 1, $\mathrm{bla}[\varphi] \models (p, q)$ if and only if $\varphi \models (p, q)$, so $\mathrm{bla}[\varphi]$ is complete; conversely, comparing $f$ and $\mathrm{bla}[\varphi]$ on singleton statements $(\{\sigma\}, f(\sigma))$ and $(\{\sigma\}, \mathrm{bla}[\varphi]\!(\sigma))$ in the three cases where either side is $\top$ or neither is forces equality. Parts 2 and 3 derive each statement of one specification from the singleton statements of the other by the union and consequence rules, then use [soundness of consequence between specifications](soundness-of-consequence-between-specifications.md). Small specifications are minimal rather than least: whether a least one exists is the question answered in [footprints suffice for well-founded resource](footprints-suffice-for-well-founded-resource.md) and [small specifications for non-negative resource](small-specifications-for-non-negative-resource.md).

## Sources

- M. Raza and P. Gardner, "Footprints in local reasoning", *Logical Methods in Computer Science* 5(2:4), 2009, <https://doi.org/10.2168/LMCS-5(2:4)2009>, arXiv:0903.1032v2 <https://arxiv.org/abs/0903.1032v2>, Section 2.2, Definitions 2.16–2.17, Lemmas 2.18 and 2.19; Section 3, Definitions 3.1, 3.3 and 3.6, Propositions 3.2, 3.4 and 3.7 and Corollary 3.5 (numbers from arXiv:0903.1032v2).
