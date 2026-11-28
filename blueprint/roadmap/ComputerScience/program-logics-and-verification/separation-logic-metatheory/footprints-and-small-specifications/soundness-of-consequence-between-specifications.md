# Soundness of consequence between specifications

A specification of local functions is a set of pre/postcondition pairs; a pair derived from a specification by the frame, consequence, union and intersection rules is satisfied by every local function that satisfies the specification.

Let $(\Sigma, \bullet, u)$ be a [separation algebra](../abstract-separation-logic/separation-algebras.md) and call the [local actions](../abstract-separation-logic/local-actions.md) $f : \Sigma \to P(\Sigma)^\top$ *local functions*. A *statement* is a pair $(p, q)$ of predicates $p, q \subseteq \Sigma$, and a *specification* $\varphi$ is a set of statements, with *domain* $D(\varphi) = \bigcup \{p : (p, q) \in \varphi\}$. A local function $f$ *satisfies* $(p, q)$, written $f \models (p, q)$, if $f(\sigma) \sqsubseteq q$ for every $\sigma \in p$, and satisfies $\varphi$ if it satisfies each of its statements; $\varphi \models (p, q)$, *semantic consequence*, means that every local function satisfying $\varphi$ satisfies $(p, q)$. *Proof-theoretic consequence* $\varphi \vdash (p, q)$ means that $(p, q)$ is derivable from the statements of $\varphi$ by the rules

- frame: from $(p, q)$ infer $(p \ast r, q \ast r)$;
- consequence: from $p' \subseteq p$, $(p, q)$ and $q \subseteq q'$ infer $(p', q')$;
- union: from $(p_i, q_i)$ for all $i \in I$ infer $(\bigcup_{i \in I} p_i, \bigcup_{i \in I} q_i)$;
- intersection: for $I \neq \emptyset$, from $(p_i, q_i)$ for all $i \in I$ infer $(\bigcap_{i \in I} p_i, \bigcap_{i \in I} q_i)$.

Then for every specification $\varphi$ and statement $(p, q)$,

$$\varphi \vdash (p, q) \implies \varphi \models (p, q).$$

## Depends on

- [Local actions](../abstract-separation-logic/local-actions.md)
- [Separation algebras](../abstract-separation-logic/separation-algebras.md)

## Proof depends on

- [Local actions](../abstract-separation-logic/local-actions.md)

## Expansion

Each rule preserves satisfaction by any fixed local function $f$, so induction on derivations gives the claim. The frame rule is the locality condition: for $\sigma = \sigma' \bullet \sigma''$ with $\sigma'' \in p$ and $\sigma' \in r$, $f(\sigma) \sqsubseteq \{\sigma'\} \ast f(\sigma'') \sqsubseteq q \ast r$; consequence and union are immediate; intersection needs a nonempty family: the empty family would derive $(\Sigma, \Sigma)$, which a local function that faults somewhere does not satisfy. Only this soundness direction is stated here; the converse, completeness, is part of the abstract separation logic of local actions.

## Sources

- M. Raza and P. Gardner, "Footprints in local reasoning", *Logical Methods in Computer Science* 5(2:4), 2009, <https://doi.org/10.2168/LMCS-5(2:4)2009>, arXiv:0903.1032v2 <https://arxiv.org/abs/0903.1032v2>, Section 2.2, Definitions 2.12, 2.14, 2.15 and 2.20, Figure 1, and Theorem 2.21 with the soundness half of its proof (numbers from arXiv:0903.1032v2).
