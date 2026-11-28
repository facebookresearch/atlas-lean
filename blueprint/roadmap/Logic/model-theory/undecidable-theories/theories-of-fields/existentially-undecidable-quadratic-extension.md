# An existentially decidable field with an existentially undecidable quadratic extension

For every prime $p$ there is a field of characteristic $p$ whose existential theory in the language of rings is decidable, while some separable quadratic extension of it has undecidable existential theory; so existential decidability does not pass to finite extensions.

**Existential decidability.** A field $K$ is *existentially decidable* if its existential theory in the language of rings $\{+,-,\cdot,0,1\}$ (sentences $\exists \bar{x}\,\psi$ with $\psi$ quantifier-free, no parameters) is decidable; equivalently, one can decide which systems of polynomial equations and inequations with coefficients in the prime field have a solution in $K$.

**Theorem (Dittmann).** Let $p$ be a prime number. There is an existentially decidable field $K$ of characteristic $p$ with a separable quadratic extension $L/K$ whose existential theory is undecidable. Moreover $K$ can be chosen so that the relative algebraic closure of $\mathbb{F}_p$ in $K$ is finite (Theorem 1.2, Corollary 4.4).

The construction also gives (Theorem 3.6): for the specific field $\mathbf{K}$ built in Section 3, which has the same existential theory as $\mathbb{F}_p((s))$, every $\aleph_0$-saturated elementary extension $\mathbf{K}^*$ and every set $S$ of primes, there is a cyclic extension $L/\mathbf{K}^*$ of degree $4$ such that $S$ is many-one reducible to the existential theory of $L$.

## Depends on

- [Field](../../../../Algebra/rings-and-fields/field.md)
- [Complete theory of a first-order structure](../../../first-order-logic/theory-of-structure.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Separable extension](../../../../FieldTheory/extensions-and-closure/separable-extension.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Following Ershov's theory of fields with a strong local-global principle, one constructs a field $\mathbf{K}$, regular over $\mathbb{F}_p(t)$, whose existential theory equals that of $\mathbb{F}_p((s))$ and is therefore decidable (by Anscombe and Fehm), and whose degree-$4$ extensions can be given prescribed residue-field behavior. A computable family of varieties $V_l$ over $\mathbb{F}_p$, one for each prime $l$, has points in a degree-$4$ extension exactly when prescribed; by saturation one obtains $L/\mathbf{K}^*$ with $V_l(L) \neq \emptyset$ iff $l \in S$ for $l > 4$. Taking $S$ undecidable makes $L$ existentially undecidable, and since $\mathbf{K}^*$ is existentially decidable, one of the two quadratic steps $L_0/\mathbf{K}^*$ or $L/L_0$ through the intermediate quadratic field $L_0$ is the required pair. An example in characteristic $0$ had been given in Kesavan Thanagopal's thesis, with a similar technique.

## Sources

- Philip Dittmann, "Two examples concerning existential undecidability in fields", *The Journal of Symbolic Logic* 90(2):552–563, 2025, doi:10.1017/jsl.2023.87; read as arXiv:2211.01775v1, <https://arxiv.org/abs/2211.01775v1>: Theorem 1.2, Theorem 3.6, Proposition 4.3 and Corollary 4.4 of arXiv:2211.01775v1.
