# Nontriviality of Shimura's quotient

Let $J$, $\mathfrak{T}$, $f$, $K$, $\mathfrak{U}$, the abelian subvariety $C$ and the triple $(A, \nu, \theta)$ be as in
[Shimura's abelian subvariety $C$ and the quotient](abelian-subvariety-c-and-the-quotient.md). Then $J \neq C$. Hence
$\dim A > 0$, and $\theta \colon K \to \mathrm{End}(A) \otimes \mathbb{Q}$ is injective.

Shimura's proof: if $J = C$, then $\{x \in D_J \mid \delta\alpha(x) = 0 \text{ for all } \alpha \in \mathfrak{U}\} = \{0\}$, and the
[$\mathfrak{T}_{\mathbb{C}}$-isomorphism between $D_J$ and $\mathfrak{T}_{\mathbb{C}}$](cusp-forms-free-of-rank-one-over-the-hecke-algebra.md)
turns this into

$$\{\xi \in \mathfrak{T}_{\mathbb{C}} \mid \mathfrak{U}\xi = 0\} = \{0\}.$$

Taking the largest non-negative integer $q$ with $\mathfrak{K}_1 \mathfrak{R}^q \neq \{0\}$, where $\mathfrak{R}^0 = \mathfrak{T}$, the left
side contains $\mathfrak{K}_1 \mathfrak{R}^q$, a contradiction.

## Depends on

- [Shimura's abelian subvariety $C$ and the quotient $(A, \nu, \theta)$](abelian-subvariety-c-and-the-quotient.md)

## Proof depends on

- [Shimura's abelian subvariety $C$ and the quotient $(A, \nu, \theta)$](abelian-subvariety-c-and-the-quotient.md)
- [Weight-two cusp forms are free of rank one over the Hecke algebra](cusp-forms-free-of-rank-one-over-the-hecke-algebra.md)
- [Decomposition of the Hecke algebra of the modular Jacobian](decomposition-of-the-hecke-algebra.md), for $\mathfrak{T} = \mathfrak{R} \oplus \mathfrak{K}_1 \oplus \dots \oplus \mathfrak{K}_r$
- [The ideal $\mathfrak{U}$ of the Hecke algebra attached to an eigenform](ideal-of-the-hecke-algebra-attached-to-an-eigenform.md), for $\mathfrak{U}$
- [Holomorphic $1$-forms and tangent space of a complex abelian variety](holomorphic-one-forms-and-tangent-space.md), for the injectivity of $\delta$ of a surjective homomorphism
- [Quotient of an abelian variety by an abelian subvariety](../quotient-by-an-abelian-subvariety.md), for $\dim A = \dim J - \dim C$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the passage from $J = C$ to the vanishing of the $1$-forms killed by every $\delta\alpha$, $\alpha \in \mathfrak{U}$: $\delta$ of the
  surjection $J^k \to J$, $(x_i) \mapsto \sum_i \alpha_i(x_i)$, is injective, and every element of $\mathfrak{U}$ has a nonzero
  integer multiple in $\mathfrak{U} \cap \mathrm{End}(J)$;
- its transport to $\mathfrak{T}_{\mathbb{C}}$ through the $\mathfrak{T}_{\mathbb{C}}$-isomorphism $D_J \cong \mathfrak{T}_{\mathbb{C}}$;
- the existence of $q$, as $\mathfrak{R}$ is nilpotent and $\mathfrak{K}_1 \neq \{0\}$, and the vanishing of
  $\mathfrak{U} \mathfrak{K}_1 \mathfrak{R}^q$, from $\mathfrak{K}_j \mathfrak{K}_1 = \{0\}$ for $j \ge 2$ and the maximality of $q$ in the
  commutative algebra $\mathfrak{T}$;
- the injectivity of $\theta$: $K$ is a field and $\theta(1) = \mathrm{id}_A \neq 0$ once $A \neq 0$.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, pp. 526–527, proof of Theorem 1 (from "To prove $J \neq C$" to "Thus $J \neq C$, so that
  $\dim(A) > 0$, and $\theta$ is injective", with the displayed condition $(*)$ and the integer $q$).
