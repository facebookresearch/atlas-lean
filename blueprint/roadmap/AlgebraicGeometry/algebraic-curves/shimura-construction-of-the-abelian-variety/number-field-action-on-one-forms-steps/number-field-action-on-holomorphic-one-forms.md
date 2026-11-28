# Holomorphic $1$-forms of an abelian variety over $\mathbb{Q}$ with an action of a number field

Let $A'$ be an [abelian variety](../../../abelian-varieties/abelian-scheme.md) over $\mathbb{Q}$, with $\mathrm{End}(A')$ the ring of
[endomorphisms](../../../abelian-varieties/homomorphisms-of-abelian-schemes.md) of $A'_{\mathbb{C}}$, let $K$ be a subfield of $\mathbb{C}$ of finite
degree over $\mathbb{Q}$ and $I$ the set of its embeddings into $\mathbb{C}$, and let
$\theta' \colon K \to \mathrm{End}(A') \otimes \mathbb{Q}$ be a ring homomorphism with $\theta'(1) = \mathrm{id}_{A'}$ such that every
element of $\theta'(K) \cap \mathrm{End}(A')$ is defined over $\mathbb{Q}$. Then the representation $a \mapsto \delta\theta'(a)$ of $K$
on the space $D_{A'}$ of [holomorphic $1$-forms](../holomorphic-one-forms-steps/holomorphic-one-forms-and-tangent-space.md) of $A'_{\mathbb{C}}$ is a multiple
of the regular representation of $K$ over $\mathbb{Q}$: there are an integer $m \ge 0$, the multiplicity, and a basis
$\{w_{\sigma j} \mid \sigma \in I,\ 1 \le j \le m\}$ of $D_{A'}$ over $\mathbb{C}$ with

$$\delta\theta'(a)(w_{\sigma j}) = a^\sigma w_{\sigma j} \qquad (a \in K).$$

In particular $\dim A' = m\,[K : \mathbb{Q}]$.

## Depends on

- [Abelian scheme](../../../abelian-varieties/abelian-scheme.md)
- [Homomorphisms of abelian schemes and commutativity](../../../abelian-varieties/homomorphisms-of-abelian-schemes.md)
- [Holomorphic $1$-forms and tangent space of a complex abelian variety](../holomorphic-one-forms-steps/holomorphic-one-forms-and-tangent-space.md)

## Proof depends on

- [Holomorphic $1$-forms of an abelian variety over $\mathbb{Q}$ and those defined over $\mathbb{Q}$](one-forms-of-an-abelian-variety-over-q.md),
  for $D_{A'} = \mathbb{C} \otimes_{\mathbb{Q}} D_{A', \mathbb{Q}}$, compatibly with $\delta\beta$ for $\beta$ defined over $\mathbb{Q}$, and
  $\dim_{\mathbb{Q}} D_{A', \mathbb{Q}} = \dim A'$
- [Bijectivity of the evaluation homomorphism](../../../../FieldTheory/extensions-and-closure/separable-extensions-over-separably-closed-field/sep-closed-tensor-hom-bijective.md),
  for the isomorphism $\mathbb{C} \otimes_{\mathbb{Q}} K \to \mathbb{C}^I$, $c \otimes a \mapsto (c\, a^\sigma)_{\sigma \in I}$
- [Holomorphic $1$-forms and tangent space of a complex abelian variety](../holomorphic-one-forms-steps/holomorphic-one-forms-and-tangent-space.md),
  for the $\mathbb{Q}$-linear extension of $\delta$ to $\mathrm{End}(A') \otimes \mathbb{Q}$, which reverses products
- [Homomorphisms of abelian schemes and commutativity](../../../abelian-varieties/homomorphisms-of-abelian-schemes.md), for $\mathrm{End}(A')$

## Proof sketch

Every element of $\mathrm{End}(A') \otimes \mathbb{Q}$ has a positive integer multiple in $\mathrm{End}(A')$; so for $a \in K$ some
$n \ge 1$ has $\theta'(n a) = n\, \theta'(a) \in \theta'(K) \cap \mathrm{End}(A')$, which is defined over $\mathbb{Q}$, and
$\delta\theta'(a) = n^{-1} \delta\theta'(n a)$ preserves the $\mathbb{Q}$-structure $D_{A', \mathbb{Q}}$. As $K$ is commutative and
$\delta$ reverses products, $a \mapsto \delta\theta'(a)$ is a homomorphism of $\mathbb{Q}$-algebras, unital as
$\theta'(1) = \mathrm{id}_{A'}$, which makes $D_{A', \mathbb{Q}}$ a $K$-vector space, of some dimension $m$, so
$D_{A', \mathbb{Q}} \cong K^m$ and $\dim A' = m\,[K : \mathbb{Q}]$. Then
$D_{A'} \cong \mathbb{C} \otimes_{\mathbb{Q}} K^m \cong (\mathbb{C}^I)^m$, compatibly with the action of $K$, which on the
$\sigma$-th coordinate of each factor is multiplication by $a^\sigma$; the corresponding basis vectors are the $w_{\sigma j}$.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 527, proof of Theorem 1 ("hence the representation of $K$ on $D_{A'}$ via $\theta'$ is a multiple of a
  regular representation of $K$ over $\mathbf{Q}$", and the basis $\{w_{\sigma j} \mid \sigma \in I, 1 \leqq j \leqq m\}$ with
  $\delta\theta'(a)(w_{\sigma j}) = a^\sigma w_{\sigma j}$).
