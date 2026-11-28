# Finite satisfiability of MSO with a non-regular cardinality relation is undecidable

Whether a monadic second-order sentence over $\{<,R\}$ holds in some finite initial segment of the naturals, with $R$ restricted to it, is undecidable for every cardinality relation $R$ not definable in $(\mathbb{N},<)$; this answers Courcelle's question for predicates "$|X| \in A$".

**Setting.** For $q \geq 1$ let $\mathcal{M}_q = ([0,q), <, R)$, where $<$ and the [cardinality relation](cardinality-relations-on-finite-sets.md) $R \subseteq \mathcal{F}^n$ are restricted to the domain $[0,q) = \{0,\dots,q-1\}$. The *satisfiability problem for $\mathrm{MSO}_{\{<,R\}}$ over finite orderings* asks, for a monadic second-order sentence over $\{<,R\}$, whether it holds in at least one $\mathcal{M}_q$ (on finite domains MSO and WMSO coincide). The relation $R$ is fixed; the sentence is the input.

**Theorem (Bès).** Let $n \geq 1$ and let $R \subseteq \mathcal{F}^n$ be a cardinality relation that is not WMSO-definable in $(\mathbb{N},<)$. Then the satisfiability problem for $\mathrm{MSO}_{\{<,R\}}$ over finite orderings is undecidable (Theorem 4.7).

For the signature $\{<\}$ alone the problem is decidable (Proposition 4.1).

## Depends on

- [Cardinality relations on finite sets of naturals](cardinality-relations-on-finite-sets.md)
- [Monadic second-order logic over words](../../../../TheoryOfComputation/omega-automata-and-games/logic-and-tree-automata/monadic-second-order-logic-over-words.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

First, for $R = \mathrm{EqCard}$ the defining formulas for $+$ and $\times$ remain correct on every $\mathcal{M}_q$, so the problem reduces from Trakhtenbrot's undecidability of satisfiability over finite orderings with the restricted graphs of $+$ and $\times$ (Propositions 4.2 and 4.4). For general $R$ the infinite-case definition of $\mathrm{EqCard}$ fails, because the auxiliary sets range only over the finite domain. Instead a "quasi-equicardinality" relation $\varphi$ is $\{<,R\}$-definable (Proposition 4.6): it implies equicardinality and agrees with it on an arbitrarily large initial segment of a large enough $\mathcal{M}_q$. A sentence $G$ over $\{<,\mathrm{EqCard}\}$ is mapped to "there is a nonempty initial segment $X$ on which $\varphi(Y,Y)$ holds for all $Y \subseteq X$, and $G$ holds relativized to $X$ with $\mathrm{EqCard}$ replaced by $\varphi$"; this is satisfiable iff $G$ is.

## Sources

- Alexis Bès, "Expansions of MSO by cardinality relations", *Logical Methods in Computer Science* 9(4):18, 2013, doi:10.2168/LMCS-9(4:18)2013; read as arXiv:1310.8182v2, <https://arxiv.org/abs/1310.8182v2>: Theorem 4.7, Propositions 4.1, 4.2, 4.4 and 4.6 of arXiv:1310.8182v2.
