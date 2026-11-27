# Rings of integers of totally imaginary quadratic extensions of certain totally real fields are undecidable

Let $K_1$ be the maximal totally real subfield of the compositum of all quadratic extensions of $\mathbb{Q}(\zeta_n + \bar\zeta_n : n \in S)$ for an infinite set $S$. For every totally real $K \supseteq K_1$ and every totally imaginary quadratic extension $L$ of $K$, the ring of integers of $L$ has undecidable first-order theory.

For $n \ge 1$ let $\zeta_n$ be a primitive $n$-th root of unity and $\bar\zeta_n$ its complex conjugate. For a field $F$, let $F^{(2)}$ be the compositum (in a fixed algebraic closure) of all extensions of $F$ of degree at most $2$. A field of algebraic numbers is *totally real* when all its embeddings into $\mathbb{C}$ are real, and *totally imaginary* when none is; these fields may have infinite degree over $\mathbb{Q}$.

**Theorem (Springer).** Let $S$ be an infinite set of positive integers, let

$$
K_0 = \mathbb{Q}\bigl(\{\zeta_n + \bar\zeta_n : n \in S\}\bigr),
$$

and let $K_1$ be the maximal totally real subfield of $K_0^{(2)}$. If $K$ is any totally real extension of $K_1$ and $L$ is any totally imaginary quadratic extension of $K$, then the first-order theory of the ring of integers $\mathcal{O}_L$, in the language of rings, is undecidable.

Conventions: $\mathcal{O}_L$ is the integral closure of $\mathbb{Z}$ in $L$; the theory is the set of sentences of the language $\{+, \cdot, 0, 1\}$ with equality true in $\mathcal{O}_L$. Unlike earlier results of this kind, $L$ may contain infinitely many roots of unity.

## Depends on

- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)
- [Integral closure of ℤ in a field and the ring of integers of a number field](../number-fields-embeddings/ring-of-integers.md)

## Proof depends on

None.

## Expansion

The proof follows the blueprint of Julia Robinson as extended by Henson: a ring of algebraic integers has undecidable theory as soon as it has a family of subsets, parametrized by one formula of the language of rings, that contains finite sets of arbitrarily large cardinality (Lemma 4.1 of arXiv:2207.00140v3). For a set $X$ of totally real algebraic numbers and $t \in \mathbb{R}$, write $X_t$ for the elements of $X$ all of whose conjugates lie in $(0, t)$; the JR-number of $X$ is the infimum of the $t$ with $X_t$ infinite. Since $2 + \zeta_n + \bar\zeta_n$ has all conjugates in $(0, 4)$ for every $n \in S$ with $n \ge 3$ (for $n = 1, 2$ it equals $4$ or $0$), and by Kronecker's theorem these are the only totally real algebraic integers with this property, $\mathrm{JR}(\mathcal{O}_{K_0}) = \mathrm{JR}(\mathcal{O}_K) = 4$, and it is attained as a minimum. Using unit groups of orders in $\mathcal{O}_L$, Springer finds an existentially definable subset $X \subseteq \mathcal{O}_L$ with $\mathcal{O}_{K_0} \subseteq X \subseteq \mathcal{O}_K$ (Theorem 3.3 of the same version). Siegel's theorem that the totally nonnegative elements of a totally real field are sums of four squares turns the condition $0 \ll x \ll a/b$, for rational $a/b$, into an existential formula with variables in $X$. The resulting sets lie between $(\mathcal{O}_{K_0})_{a/b}$ and $(\mathcal{O}_K)_{a/b}$, so they are finite and of unbounded size as $a/b$ increases to $4$, and the Robinson–Henson criterion applies. Theorem 4.4 of the same version proves this for every $K_0$ whose JR-number is infinite or an attained minimum and every totally real $K \supseteq K_1$ with $\mathrm{JR}(\mathcal{O}_K) = \mathrm{JR}(\mathcal{O}_{K_0})$; the statement here is the case of minimal JR-number.

## Sources

- Caleb Springer, *Definability and decidability for rings of integers in totally imaginary fields*, Bull. Lond. Math. Soc. 56 (2024), no. 1, 306–318, https://doi.org/10.1112/blms.12933; Theorem 1.4 of arXiv:2207.00140v3, restated and proved as Theorem 4.5 of that version, with the Robinson–Henson criterion as Lemma 4.1.
