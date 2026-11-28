# Equational theories of semirings with fixed points are Σ⁰₁-complete

Every recursively enumerable equational theory of semirings with a fixed-point operator that extends a few basic axioms and is sound for the model of languages is $\Sigma^0_1$-complete; this covers Conway and Park μ-semirings and Chomsky algebras.

**μ-expressions.** Over a finite alphabet $\Sigma$ and a countable set of variables, μ-expressions are $e ::= 0 \mid 1 \mid a \mid x \mid e + f \mid e \cdot f \mid \mu x\, e$ with $a \in \Sigma$. In the *language model* $\mathcal{L}$, closed expressions denote languages over $\Sigma$: $0$, $1$, $a$ denote $\emptyset$, $\{\epsilon\}$, $\{a\}$, $+$ is union, $\cdot$ is concatenation, and $\mu x\, e(x)$ denotes the least fixed point $\bigcap\{A : e(A) \subseteq A\}$; these are exactly the context-free languages.

**Theories.** The equational theory $\mu\mathsf{S}$ consists of the semiring axioms for $(0, 1, +, \cdot)$ (associativity and commutativity of $+$ with unit $0$, associativity of $\cdot$ with unit $1$, $0$ absorbing, distributivity on both sides) and the fixed-point axiom $\mu x\, e(x) = e(\mu x\, e(x))$; it does not require least fixed points nor the congruence rule for $\mu$. $\mu\mathsf{S}_{\not 1}$ is the same without $1$ and the axioms mentioning it, and $\mathsf{idem}$ is the axiom $e + e = e$. A theory $\mathsf{U}$ is *sound for $\mathcal{L}$* if every equation it proves holds in $\mathcal{L}$ for all closed instances, with the usual equational reasoning of the [equational calculus](equational-calculus.md).

**Theorem (Das, De and Kuznetsov).**

1. Every recursively enumerable extension of $\mu\mathsf{S} + \mathsf{idem}$ that is sound for $\mathcal{L}$ is $\Sigma^0_1$-complete (Theorem 24).
2. Every recursively enumerable extension of $\mu\mathsf{S}_{\not 1}$ that is sound for $\mathcal{L}$ is $\Sigma^0_1$-complete (Theorem 37).

Consequently the equational theories of idempotent Conway μ-semirings, idempotent Park μ-semirings and Chomsky algebras are $\Sigma^0_1$-complete (Corollary 28), and so are those of Conway μ-semirings and Park μ-semirings, also in their identity-free versions (Corollary 38).

## Depends on

- [Equational calculus](equational-calculus.md)
- [Context-free languages](../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/context-free-languages.md)
- [The arithmetical class $\Sigma_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

None.

## Expansion

The proof uses effective inseparability. Productive context-free grammars have solutions in the basic theories, expressed by μ-expressions (via Bekić's lemma). For productive grammars, the set $\mathbf{R}$ of *regularly total* grammars (which contain productions $S \Rightarrow aYT$, $T \Rightarrow a$, $T \Rightarrow aT$ for all letters $a$, and for some $n > 0$ generate from $S$ all nonempty words of length at most $n+1$ and from $Y$ all words of length $n$) and the set of grammars that do not generate all nonempty words form an effectively inseparable pair (Theorem 20), by reduction from halting and looping of Turing machines, and any r.e. set separating an effectively inseparable pair is $\Sigma^0_1$-complete (Theorem 18). For a theory $\mathsf{U}$ as in the theorem, the productive grammars $G$ for which $\mathsf{U}$ proves that the solution $e^G_S$ of the start symbol contains all nonempty words separate the pair, since $\mathsf{U}$ is sound for $\mathcal{L}$ and contains the basic axioms; hence $\mathsf{U}$ is $\Sigma^0_1$-complete. Without idempotency, the expression $\mu x(e + \mu y(x + y))$ serves as an idempotent upper bound and interprets the idempotent argument. Inclusion of context-free languages is $\Pi^0_1$-complete, so no such theory proves all true inclusions.

## Sources

- A. Das, A. De and S. L. Kuznetsov, "Undecidability for semirings with fixed points", in *11th International Conference on Formal Structures for Computation and Deduction (FSCD 2026)*, Leibniz International Proceedings in Informatics, Schloss Dagstuhl, 2026, article 15, doi:10.4230/LIPIcs.FSCD.2026.15; read as arXiv:2512.19401v1 ("Undecidability of theories of semirings with fixed points"), <https://arxiv.org/abs/2512.19401v1>: Section 2 (μ-expressions, the language model and the theories), Theorems 18, 20, 24 and 37, Corollaries 28 and 38 of arXiv:2512.19401v1.
