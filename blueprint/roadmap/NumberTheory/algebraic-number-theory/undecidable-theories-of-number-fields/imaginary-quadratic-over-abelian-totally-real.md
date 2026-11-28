# Totally imaginary quadratic extensions of certain abelian totally real fields have undecidable first-order theory

Let $K$ be an infinite totally real field inside the maximal abelian subextension of $F^{(d)}$ for a number field $F$ and $d \ge 2$, containing all roots of a suitable parametrized family of polynomials with unit constant term. Then every totally imaginary quadratic extension $L$ of $K$ has an undecidable first-order theory.

For a number field $F$ and an integer $d \ge 2$, let $F^{(d)}$ be the compositum, in a fixed algebraic closure, of all extensions of $F$ of degree at most $d$, and let $F^{(d)}_{\mathrm{ab}}$ be the maximal abelian extension of $F$ contained in $F^{(d)}$. A field of algebraic numbers is *totally real* when all its embeddings into $\mathbb{C}$ are real, and *totally imaginary* when none is.

**Theorem (Springer).** Let $K$ be an infinite totally real extension of $\mathbb{Q}$ with $K \subseteq F^{(d)}_{\mathrm{ab}}$ for some $d \ge 2$ and some number field $F$. Assume that $K$ contains all roots of every member of a parametrized family of polynomials

$$
f_a(x) = x^n + p_{n-1}(a) x^{n-1} + \cdots + p_1(a) x + p_0(a), \qquad a \in \mathbb{Z}_{> N_0},
$$

where each $p_i(t) \in \mathbb{Z}[t]$, the constant term $p_0(t) = \pm 1$ is constant, and $p_j(t)$ is nonconstant for some $1 \le j \le n - 1$. If $L$ is any totally imaginary quadratic extension of $K$, then the first-order theory of the field $L$, in the language of rings, is undecidable.

The case of $\mathbb{Q}^{(2)}$, the compositum of all quadratic fields, was proved earlier by Martínez-Ranero, Utreras and Videla; the source recovers it as a special case.

## Depends on

- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)
- [Field](../../../Algebra/rings-and-fields/field.md)
- [Integral closure of ℤ in a field and the ring of integers of a number field](../number-fields-embeddings/ring-of-integers.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Polynomials in one variable over a semiring](../../../Algebra/polynomials/univariate-polynomial-arithmetic/polynomial-ring.md)

## Proof depends on

None.

## Expansion

The proof combines three facts. The ring of integers $\mathcal{O}_L$ is first-order definable in $L$ because $L$ is a compositum of extensions of bounded degree (a definability theorem of Shlapentokh, Theorem 2.1 of the source), so it suffices to show that $\mathcal{O}_L$ is undecidable. By Bombieri and Zannier, $F^{(d)}_{\mathrm{ab}}$ has the Northcott property (Theorem 2.5), hence so does its subfield $K$, and by a result of Vidaux and Videla (Proposition 2.4) $\mathrm{JR}(\mathcal{O}_K) = \infty$, where the JR-number is the infimum of the $t$ for which infinitely many elements of $\mathcal{O}_K$ have all conjugates in $(0, t)$; this makes $\mathcal{O}_K$ undecidable by Julia Robinson's method. To transfer this to $\mathcal{O}_L$, the roots of the $f_a$ are units, and a polynomial whose values are power sums of these units cuts out, inside $\mathcal{O}_L$, a definable set of totally real elements; Lemma 2.7 enlarges it to a definable set $W$ with $\mathbb{N} \subseteq W \subseteq \mathcal{O}_K$, and Lemma 2.6 shows that such a $W$ makes $\mathcal{O}_L$ undecidable through the Robinson–Henson criterion: a ring of algebraic integers is undecidable once a family of subsets parametrized by one formula contains finite sets of arbitrarily large cardinality (Lemma 2.2; the transfer is Theorem 3.5). A good expansion links pages for Theorem 2.1, the Bombieri–Zannier theorem, Proposition 2.4, the Robinson–Henson criterion and Theorem 3.5.

## Sources

- Caleb Springer, *Undecidability, unit groups, and some totally imaginary infinite extensions of $\mathbb{Q}$*, Proc. Amer. Math. Soc. 148 (2020), 4705–4715, https://doi.org/10.1090/proc/15153; the theorem stated in the introduction of arXiv:1910.01239v2 and proved there as Theorem 3.6, from Theorem 2.1, Lemma 2.2, Proposition 2.4, Theorem 2.5 and Theorem 3.5.
