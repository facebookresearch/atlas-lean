# Logically constrained term rewriting system

A logically constrained term rewriting system (LCTRS) has rules $\ell \to r\ [\varphi]$ whose constraint $\varphi$, a formula of an underlying theory such as integer arithmetic, must hold for the values instantiating the rule's logical variables; built-in calculation steps evaluate theory symbols.

**Definition.** Fix a many-sorted signature $\mathcal F = \mathcal F_{te} \cup \mathcal F_{th}$ with a term part and a theory part. Every theory sort $\iota$ has a nonempty set $\mathcal{V}\!al_\iota \subseteq \mathcal F_{th}$ of *value* constants, with $\mathcal F_{te} \cap \mathcal F_{th} \subseteq \mathcal{V}\!al$, and an interpretation $\mathcal J$ maps ground terms over $\mathcal F_{th}$ to values, bijectively on value symbols (for the integers, $\mathbb Z \subseteq \mathcal{V}\!al$). Terms over $\mathcal F_{th}$ and variables are *logical terms*; logical terms of sort $\mathsf{bool}$ are *constraints*. A *constrained rewrite rule* is $\ell \to r\ [\varphi]$ with terms $\ell, r$ of the same sort, $\mathrm{root}(\ell) \in \mathcal F_{te} \setminus \mathcal F_{th}$ and a constraint $\varphi$; its *logical variables* are those of $\varphi$ together with the variables of $r$ not in $\ell$. An *LCTRS* $\mathcal R$ is a set of constrained rewrite rules.

A substitution $\sigma$ *respects* $\ell \to r\ [\varphi]$ if it maps every logical variable of the rule to a value and $[\![\varphi\sigma]\!] = \top$. The *calculation rules* are $f(x_1, \ldots, x_n) \to y\ [y = f(x_1, \ldots, x_n)]$ for $f \in \mathcal F_{th} \setminus \mathcal{V}\!al$. A rewrite step $s \to_{\mathcal R} t$ replaces a subterm $s|_p = \ell\sigma$ by $r\sigma$ for a rule of $\mathcal R$ or a calculation rule and a substitution $\sigma$ respecting it. $\mathcal R$ is *terminating* if $\to_{\mathcal R}$ is well-founded, *confluent* if $t \leftarrow^* s \to^* u$ implies $t \to^* v \leftarrow^* u$ for some $v$, and *locally confluent* if $t \leftarrow s \to u$ implies $t \to^* v \leftarrow^* u$ for some $v$ (see [confluence of a relation](../confluence-of-a-relation.md)).

## Depends on

- [Confluence of a relation](../confluence-of-a-relation.md)
- [Term rewriting systems](../../automated-deduction/term-rewriting-systems.md)

## Proof depends on

None.

## Expansion

An ordinary term rewriting system is an LCTRS with no theory symbols other than values and with all constraints true. LCTRSs model programs with built-in data such as integers or bit vectors: for instance a rule $\mathsf f(x) \to \mathsf f(x - 1)\ [x > 0]$ applies to $\mathsf f(5)$, and the calculation rule for $-$ then evaluates $5 - 1$ to the value $4$. Rewriting on constrained terms $s\ [\varphi]$, used for critical-pair analysis, is defined modulo an equivalence that instantiates only the variables of the constraint.

## Sources

- J. Schöpf, F. Mitterwallner and A. Middeldorp, "Confluence of Logically Constrained Rewrite Systems Revisited", in *Automated Reasoning (IJCAR 2024), Part II*, Lecture Notes in Computer Science 14740, Springer, 2024, pp. 298–316, <https://doi.org/10.1007/978-3-031-63501-4_16>; numbers from arXiv:2402.13552v5, <https://arxiv.org/abs/2402.13552v5>: Section 2 (preliminaries on LCTRSs, calculation rules, rewrite steps and confluence).
