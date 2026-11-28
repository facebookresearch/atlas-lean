# Presburger arithmetic with predicates for the powers of k and of ℓ is undecidable

For multiplicatively independent integers k, ℓ ≥ 2, the first-order theory of the natural numbers with addition and predicates for the powers of k and the powers of ℓ is undecidable, settling the case k = 2, ℓ = 3 open since the 1980s.

**Theorem (Hieronymi and Schulz).** For $k \in \mathbb N_{\ge 2}$ let $k^{\mathbb N} = \{k^i : i \in \mathbb N\}$. Let $k, \ell \in \mathbb N_{\ge 2}$ be [multiplicatively independent](../../../../NumberTheory/digits-numeration/numeration-automatic/cobham-s-theorems-on-recognizable-sets/bases-multiplicatively-independent.md), that is, $k^m \neq \ell^n$ for all positive integers $m, n$. Then:

1. the first-order theory $\mathrm{FO}(\mathbb N, +, k^{\mathbb N}, \ell^{\mathbb N})$ is undecidable (Theorem B of the source);
2. more generally, if $X \subseteq \mathbb N^m$ is [$k$-recognizable](../../../../NumberTheory/digits-numeration/numeration-automatic/cobham-s-theorems-on-recognizable-sets/is-base-recognizable.md), $Y \subseteq \mathbb N^n$ is $\ell$-recognizable, and neither is first-order definable in $(\mathbb N, +)$, then $\mathrm{FO}(\mathbb N, +, X, Y)$ is undecidable (Theorem A).

By Büchi's theorem, each $\mathrm{FO}(\mathbb N, +, V_k)$ is decidable, where $V_k(x)$ is the largest power of $k$ dividing $x$; Villemaire showed that $\mathrm{FO}(\mathbb N, +, V_k, V_\ell)$ is undecidable, and Bès extended this to $(\mathbb N, +, V_k, L)$ for $\ell$-recognizable $L$ not definable in $(\mathbb N, +)$. Part 2 implies the Cobham–Semënov theorem: a set that is both $k$- and $\ell$-recognizable is definable in $(\mathbb N, +)$. The structure $(\mathbb N, +, k^{\mathbb N}, \ell^{\mathbb N})$ does not define multiplication, so the undecidability is not obtained by interpreting arithmetic.

## Depends on

- [Multiplicatively independent bases](../../../../NumberTheory/digits-numeration/numeration-automatic/cobham-s-theorems-on-recognizable-sets/bases-multiplicatively-independent.md)
- [Sets recognizable in base k](../../../../NumberTheory/digits-numeration/numeration-automatic/cobham-s-theorems-on-recognizable-sets/is-base-recognizable.md)
- [Complete theory of a first-order structure](../../../first-order-logic/theory-of-structure.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Part 2 reduces to part 1, since by Bès, $k^{\mathbb N}$ is definable in $(\mathbb N, +, X)$ for any $k$-recognizable $X$ not definable in $(\mathbb N, +)$. For part 1, for $x \in k^{\mathbb N}$ let $S(x) \subseteq \ell^{\mathbb N}$ be the set of $y \in \ell^{\mathbb N}$ such that $x$ is the second largest power of $k$ with a nonzero digit in the base-$k$ expansion of $y$; for instance $3^3 = 2^4 + 2^3 + 2 + 1$, so $3^3 \in S(2^3)$. The sets $S(x)$ are uniformly definable in $(\mathbb N, +, k^{\mathbb N}, \ell^{\mathbb N})$, each is finite by a corollary of Baker's theorem on linear forms in logarithms, and every pattern of finite sets occurs among tuples $(S(k^m), \ldots, S(k^{m+n}))$ (Lemma 3.4). This lets formulas quantify over tuples of finite subsets of $\mathbb N^2$, and, following the undecidability proof for the weak monadic second-order theory of the grid, the halting problem is encoded.

## Sources

- P. Hieronymi and C. Schulz, "A strong version of Cobham's theorem", in *STOC '22: Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing*, ACM, 2022, pp. 1172–1179, <https://doi.org/10.1145/3519935.3519958>; numbers from arXiv:2110.11858v2, <https://arxiv.org/abs/2110.11858v2>: Section 1 (Theorems A and B, Facts 1.1 and 1.2, the history and the outline of the proof) and Lemma 3.4.
