# The Eichler–Deuring mass formula for supersingular elliptic curves

Summing $1/\#\operatorname{Aut}(E)$ over the isomorphism classes of supersingular elliptic curves in characteristic $p$ gives $(p-1)/24$, for every prime $p$.

Let $p$ be a prime and $\bar{\mathbb{F}}_p$ an algebraic closure of $\mathbb{F}_p$. Then

$$
\sum_{[E]}\frac{1}{\#\operatorname{Aut}(E)}=\frac{p-1}{24},
$$

the sum running over the isomorphism classes of [supersingular](is-supersingular.md) elliptic curves $E$ over $\bar{\mathbb{F}}_p$, and $\operatorname{Aut}(E)$ the [automorphism group](../automorphism-group-of-an-elliptic-curve.md) of $E$. Equivalently, $\sum_{[E]}2/\#\operatorname{Aut}(E)$ is the [Eichler mass](../../../NumberTheory/not-yet-classified/supersingular-jset/eichler-mass.md) of level $1$, $(p-1)\psi(1)/12=(p-1)/12$.

For example, for $p=2$ the only class has $j=0$ and $24$ automorphisms; for $p=3$ it has $12$, giving $1/12=2/24$; for $p=11$ the classes $j=1728$ and $j=0$ give $1/4+1/6=10/24$.

## Depends on

- [Supersingular elliptic curves](is-supersingular.md)
- [Automorphism groups of elliptic curves](../automorphism-group-of-an-elliptic-curve.md)
- [Eichler Mass](../../../NumberTheory/not-yet-classified/supersingular-jset/eichler-mass.md)

## Proof depends on

- [The Deuring correspondence between supersingular curves and maximal orders](../../../ComputerScience/cryptography/public-key/isogeny-and-lattice-foundations/supersingular-isogenies-and-quaternion-orders/deuring-correspondence.md)

## Expansion

The Eichler mass formula for a maximal order $\mathcal{O}$ in the definite quaternion algebra $B$ over $\mathbb{Q}$ of discriminant $p$ states $\sum_{[J]}1/w_J=\varphi(p)/12=(p-1)/12$, over the right ideal classes, with $w_J=\#\bigl(\mathcal{O}_L(J)^\times/\{\pm1\}\bigr)=\#\mathcal{O}_L(J)^\times/2$. The Deuring correspondence matches the isomorphism classes of supersingular curves with these ideal classes and $\operatorname{Aut}(E)$ with $\mathcal{O}_L(J)^\times$, so $\#\operatorname{Aut}(E)=2w_J$ and the sum is $(p-1)/24$. A good expansion adds pages for the Eichler mass formula over $\mathbb{Q}$, for the Deuring correspondence with its identification of automorphism groups, and for the zeta-function computation behind the mass formula. The NumberTheory folder of supersingular $j$-invariants defines the Eichler mass and an automorphism weight whose reciprocal sum this formula evaluates.

## Sources

- John Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer (2021), [doi:10.1007/978-3-030-56694-4](https://doi.org/10.1007/978-3-030-56694-4); numbers from the author's corrected edition v.1.0.7u, [author's copy](https://jvoight.github.io/quat-book.pdf), Theorem 25.1.1, Corollary 42.3.7, paragraph 42.3.8 and equation (42.3.9), Example 42.3.11.
