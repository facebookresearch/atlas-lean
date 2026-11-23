# Grothendieck–Messing deformation theorem

Let $R$ be a commutative ring and $I \subset R$ an ideal. A divided power structure on $I$ is a family
of maps $\gamma_i \colon I \to R$, $i \ge 0$, with $\gamma_0(x) = 1$, $\gamma_1(x) = x$,
$\gamma_i(x) \in I$ for $i \ge 1$, $\gamma_j(x + y) = \sum_{0 \le i \le j} \gamma_i(x)\gamma_{j-i}(y)$,
$\gamma_i(ax) = a^i \gamma_i(x)$ for $a \in R$ and $i \ge 1$,
$\gamma_i(x)\gamma_j(x) = \binom{i+j}{i} \gamma_{i+j}(x)$ and
$\gamma_i(\gamma_j(x)) = \frac{(ij)!}{i!\,(j!)^i} \gamma_{ij}(x)$ for $i, j \ge 1$; it is nilpotent if
there is $n_0$ with $\gamma_i(x) = 0$ for all $i \ge n_0$ and $x \in I$. A nilpotent divided power
extension of a ring $R_0$ is such a triple $(R, I, (\gamma_i))$ with an isomorphism $R/I \cong R_0$.

**Theorem** (Grothendieck, Messing). Let $p$ be a prime and $X_0$ a
[$p$-divisible group](p-divisible-group.md) over a ring $R_0$. Consider nilpotent divided power
extensions $(R, I, (\gamma_i))$ of $R_0$ in which $p$ is nilpotent.

1. To each such extension there is functorially attached a locally free $R$-module $\mathbb{D}(X_0)_R$
   of rank the height of $X_0$, the value of the covariant Dieudonné crystal of $X_0$.
2. If $X$ is a $p$-divisible group over $R$ lifting $X_0$, there is a functorial exact sequence
   $0 \to \operatorname{Lie}(X^t/R)^\vee \to \mathbb{D}(X_0)_R \to \operatorname{Lie}(X/R) \to 0$,
   where $\operatorname{Lie}(X/R)$ is the tangent space of $X$, a projective $R$-module of rank the
   dimension of $X$, and $\operatorname{Lie}(X^t/R)^\vee$ is the $R$-dual of the tangent space of the
   Serre dual $X^t$.
3. If $A$ is an [abelian scheme](abelian-scheme.md) over $R$ with an isomorphism
   $A[p^\infty] \times_R R_0 \cong X_0$, there is a natural isomorphism
   $\mathbb{D}(X_0)_R \cong H_1^{\mathrm{dR}}(A/R)$ with the first de Rham homology of $A$, which
   identifies the sequence of (2) for $A[p^\infty]$ with the Hodge filtration
   $0 \to \operatorname{Lie}(A^t/R)^\vee \to H_1^{\mathrm{dR}}(A/R) \to \operatorname{Lie}(A/R) \to 0$.
4. Lifts of $X_0$ to $R$ are equivalent to lifts of its Hodge filtration: the functor sending a lift
   $X$ to the sequence of (2), with its identification modulo $I$ with the sequence of $X_0$, is an
   equivalence from $p$-divisible groups over $R$ lifting $X_0$ to the category of exact sequences
   $0 \to F \to \mathbb{D}(X_0)_R \to Q \to 0$ of projective $R$-modules together with an isomorphism
   of their reduction modulo $I$ with $0 \to \operatorname{Lie}(X_0^t)^\vee \to \mathbb{D}(X_0)_{R_0}
   \to \operatorname{Lie}(X_0) \to 0$.

Chai and Oort use the theorem as a black box; for the trivial divided powers on an ideal of square
zero it reduces deformations of abelian schemes over square-zero thickenings to lifts of Hodge
filtrations.

This node is still to be broken down: the statement is precise, but its proof is not. A good
expansion follows Messing's book and has pages for the universal extension of a $p$-divisible group by
a vector group and its Lie algebra, the construction of the Dieudonné crystal $\mathbb{D}(X_0)$ and its
values on nilpotent divided power thickenings, the comparison (3) with de Rham homology for abelian
schemes, the equivalence (4), and the deduction of the
[Serre–Tate theorem](serre-tate-theorem.md) (Messing, chapter "The deformation theory and
applications", pp. 150–174).

## Depends on

- [p-divisible group](p-divisible-group.md)
- [Abelian scheme](abelian-scheme.md), for item (3)

## Sources

- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): (2.2)
  (divided powers and nilpotent divided power extensions; the formulas there for $\gamma_i(ax)$ and
  $\gamma_i(x)\gamma_j(x)$ are stated with misprints), (2.3) and Theorem 2.4 (i)–(iv)
  (Grothendieck–Messing, as a black box; the hypothesis that $p$ is nilpotent in $R$, part of
  Messing's setting, is left implicit there).
- W. Messing, *The Crystals Associated to Barsotti–Tate Groups: with Applications to Abelian Schemes*,
  Lecture Notes in Mathematics 264, Springer, 1972, chapter "The deformation theory and applications"
  (pp. 150–174).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, for rings in which $p$ is nilpotent with nilpotent
  divided powers, as `GlobalTheory.Published.GrothendieckMessing`.
