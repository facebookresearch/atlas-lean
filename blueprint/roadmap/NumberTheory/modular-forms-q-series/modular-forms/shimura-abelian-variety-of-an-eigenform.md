# Shimura's abelian variety attached to a weight-two eigenform

Let $N$ be a positive integer and $\Gamma$ a group of level $N$, that is,
$\Gamma_1(N) \subset \Gamma \subset \Gamma_0(N)$. Let $J$ be the Jacobian of the
[modular curve $X_\Gamma$](modular-curve-of-a-group-of-level-n.md) over $\mathbb{Q}$, let
$\xi_n \in \mathrm{End}(J)$ be the [Hecke endomorphisms](hecke-endomorphisms-of-the-modular-jacobian.md)
and $T_n$ the [Hecke operators](hecke-operators-of-level-n.md) on the space $S_2(\Gamma)$ of
[cusp forms](cusp-form.md) of weight $2$ for $\Gamma$. Let

$$f(z) = \sum_{n = 1}^{\infty} a_n e^{2 \pi i n z}, \qquad a_1 = 1,$$

be an element of $S_2(\Gamma)$ that is a common eigenfunction of the $T_n$ for all $n$, that is,
$f \mid T_n = a_n f$ for all $n \ge 1$, and let $K$ be the subfield of $\mathbb{C}$ generated over
$\mathbb{Q}$ by the $a_n$ for all $n$.

Then there is a triple $(A, \nu, \theta)$ with the following properties.

- (i) $(A, \nu)$ is a [quotient](../../../AlgebraicGeometry/abelian-varieties/quotient-by-an-abelian-subvariety.md)
    of $J$ by an abelian subvariety rational over $\mathbb{Q}$: $A$ is an abelian variety over
    $\mathbb{Q}$ and $\nu \colon J \to A$ is a surjective homomorphism over $\mathbb{Q}$ whose kernel is
    an abelian subvariety of $J$ defined over $\mathbb{Q}$.
- (ii) $\theta$ is an isomorphism of $K$ into $\mathrm{End}(A) \otimes \mathbb{Q}$, that is, an injective map
    preserving sums and products, with

    $$\nu \circ \xi_n = \theta(a_n) \circ \nu \quad \text{in } \mathrm{Hom}(J, A) \otimes \mathbb{Q}
    \qquad \text{for all } n \ge 1,$$

    where $\mathrm{End}(A)$ and $\mathrm{Hom}(J, A)$ are the endomorphisms and homomorphisms defined
    over $\mathbb{C}$, that is, of $A_{\mathbb{C}}$ and from $J_{\mathbb{C}}$ to $A_{\mathbb{C}}$. Since
    $a_1 = 1$ and $\xi_1$ is the identity, this gives $\theta(1) = \mathrm{id}_A$. (The proof shows that
    the elements of $\theta(K) \cap \mathrm{End}(A)$ are then rational over $\mathbb{Q}$.)
- (iii) $\dim A = [K : \mathbb{Q}]$; in particular $K$ is a finite extension of $\mathbb{Q}$.

Under the conditions (i) and (ii) the triple is unique up to isomorphism over $\mathbb{Q}$: if
$(A', \nu', \theta')$ also satisfies (i) and (ii), there is an isomorphism $\varphi \colon A \to A'$ over
$\mathbb{Q}$ with $\varphi \circ \nu = \nu'$ and $\theta'(a) \circ \varphi = \varphi \circ \theta(a)$ for all
$a \in K$. (The proof shows that $\nu'$ has the same kernel as $\nu$, so that $(A, \nu)$ and
$(A', \nu')$ are quotients of $J$ by the same abelian subvariety; $\theta'$ is then determined by (ii),
because $\nu'$ is surjective and the $a_n$ generate $K$.)

This is the part of Shimura's Theorem 1 that constructs $A$. The theorem further states that for
every embedding $\sigma \colon K \to \mathbb{C}$ there is an $f_\sigma \in S_2(\Gamma)$ with
$f_\sigma(z) = \sum a_n^\sigma e^{2 \pi i n z}$ and $f_\sigma \mid T_n = a_n^\sigma f_\sigma$ (printed
"$f_\sigma \mid T_n = a_n^\sigma f$", a misprint), gives a description
(iv) of the holomorphic differentials of $A$ pulled back to $J$ in terms of the $f_\sigma$, and, when
$\Gamma = \Gamma_0(N)$ or $\sum_\sigma \mathbb{C} f_\sigma$ is stable under $h(z) \mapsto h(-1/Nz) / z^2$, an
identity between the one-dimensional part of the zeta function of $A$ over $\mathbb{Q}$ and
$\prod_\sigma \sum_n a_n^\sigma n^{-s}$ up to finitely many Euler factors; neither is part of this page.

## Depends on

- [Modular curve of a group of level $N$ and its standard model over $\mathbb{Q}$](modular-curve-of-a-group-of-level-n.md)
- [Jacobian of a smooth proper curve](../../../AlgebraicGeometry/algebraic-curves/jacobians-of-curves/jacobian.md), for $J$
- [Hecke endomorphisms $\xi_n$ of the Jacobian of a modular curve](hecke-endomorphisms-of-the-modular-jacobian.md)
- [Hecke operators $T_n$ on weight-two cusp forms for a group of level $N$](hecke-operators-of-level-n.md)
- [Cusp form](cusp-form.md), for $S_2(\Gamma)$
- [Congruence subgroup $\Gamma_0(N)$](congruence-subgroup-gamma0.md)
- [Congruence subgroup $\Gamma_1(N)$](congruence-subgroup-gamma1.md)
- [Quotient of an abelian variety by an abelian subvariety](../../../AlgebraicGeometry/abelian-varieties/quotient-by-an-abelian-subvariety.md)
- [Abelian scheme](../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md), for abelian varieties over $\mathbb{Q}$ and their dimension
- [Homomorphisms of abelian schemes and commutativity](../../../AlgebraicGeometry/abelian-varieties/homomorphisms-of-abelian-schemes.md), for $\mathrm{Hom}(J, A)$ and $\mathrm{End}(A)$

## Proof depends on

- [Shimura's abelian subvariety $C$ and the quotient $(A, \nu, \theta)$](../../../AlgebraicGeometry/abelian-varieties/shimura-construction-of-the-abelian-variety/abelian-subvariety-c-and-the-quotient.md), for a triple
  satisfying (i) and the relation of (ii)
- [Nontriviality of Shimura's quotient](../../../AlgebraicGeometry/abelian-varieties/shimura-construction-of-the-abelian-variety/nontriviality-of-the-quotient.md), for the injectivity of $\theta$
- [Multiplicity one and the dimension of Shimura's quotient](../../../AlgebraicGeometry/abelian-varieties/shimura-construction-of-the-abelian-variety/multiplicity-one-and-the-dimension.md), for (iii)
- [Uniqueness of Shimura's quotient](../../../AlgebraicGeometry/abelian-varieties/shimura-construction-of-the-abelian-variety/uniqueness-of-the-quotient.md), for the uniqueness under (i) and (ii)

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: Theorem 1, p. 526, conditions
  (i)–(iii) and the sentence "Under the conditions (i, ii), the triple $(A, \nu, \theta)$ is unique up to
  isomorphisms over $\mathbb{Q}$", with the setting of §1, pp. 525–526 (the quotient of an abelian variety
  by an abelian subvariety, $T_n$ and $\xi_n$, the standard model, the eigenfunction $f$ with $a_1 = 1$
  and the field $K$); the proof, pp. 526–527 (the algebra $\mathfrak{T}$, the abelian subvariety $C$,
  [11, Th. 3.51], and the kernel of $\nu'$ in the uniqueness argument).
- G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Publ. Math. Soc.
  Japan 11, Iwanami Shoten and Princeton University Press, 1971: Theorem 3.51, §7.2 and §7.3, as
  cited in Shimura (1973) above; not read for this page.
