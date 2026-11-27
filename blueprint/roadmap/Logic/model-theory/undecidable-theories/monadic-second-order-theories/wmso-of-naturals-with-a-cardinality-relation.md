# WMSO of the naturals with a non-regular cardinality relation is undecidable

Adding to weak monadic second-order logic of $(\mathbb{N},<)$ any cardinality relation that is not already definable there makes addition and multiplication definable, so the resulting theory is undecidable; in particular this holds for "$|X| \in A$" whenever $A$ is not ultimately periodic.

**Theorem (Bès).** Let $n \geq 1$ and let $R \subseteq \mathcal{F}^n$ be a [cardinality relation](cardinality-relations-on-finite-sets.md) that is not WMSO-definable in $(\mathbb{N},<)$. Then the graphs of $+$ and $\times$ on $\mathbb{N}$ are WMSO-definable in $(\mathbb{N},<,R)$, and the WMSO theory $\mathrm{WMSO}(\mathbb{N},<,R)$ is undecidable (Theorem 3.6).

Here $\mathcal{F}$ is the set of finite subsets of $\mathbb{N}$, and set quantifiers range over $\mathcal{F}$. Special cases stated in the source: $R = \mathrm{EqCard}$ (Proposition 3.1), and every unary cardinality relation $R$ with $\mathcal{I}(R)$ not ultimately periodic (Proposition 3.2).

## Depends on

- [Cardinality relations on finite sets of naturals](cardinality-relations-on-finite-sets.md)
- [Ultimately periodic sets of natural numbers](../../../../NumberTheory/digits-numeration/numeration-automatic/cobham-s-theorems-on-recognizable-sets/is-ultimately-periodic-set.md)

## Proof depends on

- [Tarski's undefinability theorem](../../../proof-theory/g-del-s-incompleteness-theorems/tarski-s-undefinability-theorem.md)

## Expansion

For $\mathrm{EqCard}$: $z = x + y$ iff $x \leq z$ and $|(x,z]| = |[0,y)|$, and for $x, y, z \geq 1$, $z = xy$ iff some finite $A \subseteq [0,z]$ contains $0$ and $z$, has $|A| = |[0,x]|$, and consecutive elements $a_1 < a_2$ of $A$ satisfy $|[a_1,a_2)| = |[0,y)|$. Hence first-order arithmetic $\mathrm{FO}(\mathbb{N},+,\times)$ interprets into the theory, and its undecidability transfers. For a unary non-definable $R$, the formula $\forall Z\,(Z \cap (X \cup Y) = \emptyset \to (R(X \cup Z) \leftrightarrow R(Y \cup Z)))$ defines $\mathrm{EqCard}$. For general $n$, an analogue of the Michaux–Villemaire theorem (Theorem 3.4) yields a unary cardinality relation definable in $(\mathbb{N},<,R)$ but not in $(\mathbb{N},<)$. Earlier, Klaedtke and Ruess had proved undecidability for their linear-inequality predicates.

## Sources

- Alexis Bès, "Expansions of MSO by cardinality relations", *Logical Methods in Computer Science* 9(4):18, 2013, doi:10.2168/LMCS-9(4:18)2013; read as arXiv:1310.8182v2, <https://arxiv.org/abs/1310.8182v2>: Theorem 3.6, Propositions 3.1 and 3.2 and Theorem 3.4 of arXiv:1310.8182v2.
