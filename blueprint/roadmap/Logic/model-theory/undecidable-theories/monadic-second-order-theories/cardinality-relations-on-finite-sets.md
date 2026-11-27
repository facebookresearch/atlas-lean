# Cardinality relations on finite sets of naturals

A cardinality relation is a relation on finite sets of natural numbers whose truth depends only on the sizes of its arguments, such as equicardinality $|X| = |Y|$ or "$|X|$ belongs to a fixed set $A$". Expanding weak monadic second-order logic of $(\mathbb{N},<)$ by such a predicate is the setting of its undecidability results.

**Definition.** Let $\mathcal{F}$ be the set of finite subsets of $\mathbb{N}$ and $n \geq 1$. A relation $R \subseteq \mathcal{F}^n$ is a *cardinality relation* if for all $(X_1,\dots,X_n), (Y_1,\dots,Y_n) \in \mathcal{F}^n$ with $|X_i| = |Y_i|$ for every $i$,

$$
(X_1,\dots,X_n) \in R \iff (Y_1,\dots,Y_n) \in R .
$$

Its *size set* is $\mathcal{I}(R) = \{(|X_1|,\dots,|X_n|) : (X_1,\dots,X_n) \in R\} \subseteq \mathbb{N}^n$; conversely every $S \subseteq \mathbb{N}^n$ is $\mathcal{I}(R)$ for exactly one cardinality relation $R$.

**Examples.** The equicardinality relation $\mathrm{EqCard}(X,Y) \iff |X| = |Y|$; for $A \subseteq \mathbb{N}$, the unary relation $R_A(X) \iff |X| \in A$; the Klaedtke–Ruess predicates $|X_1| + \dots + |X_r| < |Y_1| + \dots + |Y_s|$.

**Definability.** In weak monadic second-order logic (WMSO), set variables range over finite subsets. A relation $R \subseteq \mathcal{F}^n$ is *definable in* $(\mathbb{N},<)$ if some WMSO formula $\varphi(X_1,\dots,X_n)$ over the signature $\{<\}$ defines it in $(\mathbb{N},<)$; $\mathrm{WMSO}(\mathbb{N},<,R)$ is the set of WMSO sentences over $\{<,R\}$ true in the expansion $(\mathbb{N},<,R)$.

## Depends on

- [Monadic second-order theory of linear orders](monadic-second-order-theory-of-linear-orders.md)
- [Weak monadic second-order logic of $k$ successors](../../../../TheoryOfComputation/omega-automata-and-games/logic-and-tree-automata/weak-monadic-second-order-logic-of-k-successors.md)

## Proof depends on

None.

## Expansion

By the Büchi–Elgot–Trakhtenbrot theorem, $\mathrm{WMSO}(\mathbb{N},<)$ is decidable and the relations definable in $(\mathbb{N},<)$ are those whose encodings as words over $\{0,1\}^n$ form a regular language. For a unary cardinality relation $R$, definability in $(\mathbb{N},<)$ holds exactly when $\mathcal{I}(R)$ is ultimately periodic (Theorem 2.5 of the source characterizes the general case). So $R_A$ is definable when $A$ is ultimately periodic, while $\mathrm{EqCard}$ is not definable, since its word encoding is not regular.

## Sources

- Alexis Bès, "Expansions of MSO by cardinality relations", *Logical Methods in Computer Science* 9(4):18, 2013, doi:10.2168/LMCS-9(4:18)2013; read as arXiv:1310.8182v2, <https://arxiv.org/abs/1310.8182v2>: Section 1 (finite sets, WMSO, Theorem 1.1), Section 2 (definition of cardinality relations, $\mathcal{I}(R)$, Examples and Theorem 2.5) of arXiv:1310.8182v2.
