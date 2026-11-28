# Uniqueness of Shimura's quotient

Let $N$, $\Gamma$, $J$, $\xi_n$, $f = \sum a_n e^{2 \pi i n z}$ and $K$ be as in
[multiplicity one and the dimension](multiplicity-one-and-the-dimension.md), and let $(A, \nu, \theta)$ and
$(A', \nu', \theta')$ be two triples, each formed by a [quotient](../../abelian-varieties/quotient-by-an-abelian-subvariety.md) of $J$ by an
abelian subvariety rational over $\mathbb{Q}$ and an injective ring homomorphism of $K$ into the endomorphisms tensored
with $\mathbb{Q}$ of that quotient, with $\nu \circ \xi_n = \theta(a_n) \circ \nu$ and $\nu' \circ \xi_n = \theta'(a_n) \circ \nu'$ for
all $n$. Then $\mathrm{Ker}(\nu) = \mathrm{Ker}(\nu')$, and there is an isomorphism $\varphi \colon A \to A'$ over $\mathbb{Q}$ with
$\varphi \circ \nu = \nu'$ and $\theta'(a) \circ \varphi = \varphi \circ \theta(a)$ for all $a \in K$.

## Proof sketch

Shimura's proof: by [multiplicity one](multiplicity-one-and-the-dimension.md),
$\delta\nu(D_A) = \delta\nu'(D_{A'}) = \mu(\sum_{\sigma \in I} \mathbb{C} f_\sigma)$, so by
[(1.2)](tangent-space-of-the-kernel-of-a-quotient.md) the tangent spaces at the origin of $\mathrm{Ker}(\nu)$ and
$\mathrm{Ker}(\nu')$ are both the annihilator of $\mu(\sum_{\sigma \in I} \mathbb{C} f_\sigma)$.

## Depends on

- [Modular curve of a group of level $N$ and its standard model over $\mathbb{Q}$](../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/modular-curve-of-a-group-of-level-n.md), for $J$ over $\mathbb{Q}$
- [Hecke endomorphisms $\xi_n$ of the Jacobian of a modular curve](../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/hecke-endomorphisms-of-the-modular-jacobian.md)
- [Hecke operators $T_n$ on weight-two cusp forms for a group of level $N$](../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curves-and-hecke-operators-of-level-n/hecke-operators-of-level-n.md), for the eigenfunction $f$
- [Quotient of an abelian variety by an abelian subvariety](../../abelian-varieties/quotient-by-an-abelian-subvariety.md)
- [Homomorphisms of abelian schemes and commutativity](../../abelian-varieties/homomorphisms-of-abelian-schemes.md)

## Proof depends on

- [Multiplicity one and the dimension of Shimura's quotient](multiplicity-one-and-the-dimension.md)
- [Tangent space of the kernel of a quotient of abelian varieties](tangent-space-of-the-kernel-of-a-quotient.md)
- [Quotient of an abelian variety by an abelian subvariety](../../abelian-varieties/quotient-by-an-abelian-subvariety.md), for the uniqueness of a quotient up to isomorphism over $\mathbb{Q}$

## Expansion

This node is still to be broken down. A good expansion states and links:

- that an abelian subvariety of $J$ is determined by its tangent space at the origin, as a connected complex Lie
  subgroup of the complex torus $J(\mathbb{C})$ is determined by its Lie algebra;
- the determination of $\theta'$ by $\nu'$: $\nu'$ is surjective, so $\theta'(a_n)$ is determined by
  $\nu' \circ \xi_n = \theta'(a_n) \circ \nu'$, and the $a_n$ generate $K$ as a $\mathbb{Q}$-algebra.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 527, proof of Theorem 1 ("By (1.2), the tangent space of $\mathrm{Ker}(\nu')$ at the origin is the annihilator
  of $\mu(\sum_{\sigma \in I} \mathbf{C} f_\sigma)$. This proves the uniqueness of $(A, \nu, \theta)$"); Theorem 1, p. 526
  ("Under the conditions (i, ii), the triple $(A, \nu, \theta)$ is unique up to isomorphisms over $\mathbf{Q}$").
