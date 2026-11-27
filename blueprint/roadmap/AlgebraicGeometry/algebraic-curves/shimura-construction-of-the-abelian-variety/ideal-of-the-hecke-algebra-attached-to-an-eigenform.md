# The ideal $\mathfrak{U}$ of the Hecke algebra attached to an eigenform

Let $\mathfrak{T} = \mathfrak{R} \oplus \mathfrak{S}$, $\mathfrak{S} = \mathfrak{K}_1 \oplus \dots \oplus \mathfrak{K}_r$, be the
[decomposition of the Hecke algebra](decomposition-of-the-hecke-algebra.md) of the Jacobian $J$ of the modular curve of
a group $\Gamma$ of level $N$, and let $\rho \colon \mathfrak{T} \to K$ be the
[homomorphism onto the field of a normalized common eigenfunction $f$](homomorphism-of-the-hecke-algebra-onto-the-coefficient-field.md).
After renumbering the $\mathfrak{K}_i$, $\rho$ maps $\mathfrak{K}_1$ isomorphically onto $K$; let
$\rho' \colon K \to \mathfrak{K}_1$ be the inverse isomorphism and

$$\mathfrak{U} = \mathfrak{K}_2 + \dots + \mathfrak{K}_r + \mathfrak{R}.$$

Then $\mathfrak{U}$ is the kernel of $\rho$; in particular $\mathfrak{U}$ is an ideal of $\mathfrak{T}$, and
$t - \rho'(\rho(t)) \in \mathfrak{U}$ for every $t \in \mathfrak{T}$, so that $\xi_n - \rho'(a_n) \in \mathfrak{U}$ for all $n$ and
$1 - \rho'(1) \in \mathfrak{U}$.

Shimura states that $\mathfrak{U}$ is an ideal and that $\xi_n - \rho'(a_n) \in \mathfrak{U}$; the identification of
$\mathfrak{U}$ with the kernel of $\rho$ is the argument behind both.

## Depends on

- [Decomposition of the Hecke algebra of the modular Jacobian](decomposition-of-the-hecke-algebra.md)
- [Homomorphism of the Hecke algebra onto the field of an eigenform](homomorphism-of-the-hecke-algebra-onto-the-coefficient-field.md)

## Proof depends on

- [Decomposition of the Hecke algebra of the modular Jacobian](decomposition-of-the-hecke-algebra.md)
- [Homomorphism of the Hecke algebra onto the field of an eigenform](homomorphism-of-the-hecke-algebra-onto-the-coefficient-field.md)

## Expansion

This node is still to be broken down. A good expansion states and links:

- the vanishing of $\rho$ on $\mathfrak{R}$, a nilpotent ideal of the finite-dimensional algebra $\mathfrak{T}$, since $K$ is a
  field;
- the fact that a homomorphism of a finite product of fields onto a field vanishes on all factors but one and is an
  isomorphism on that one, applied to $\rho$ on $\mathfrak{S}$;
- the resulting equality $\ker \rho = \mathfrak{U}$, from $\mathfrak{T} = \mathfrak{K}_1 \oplus \mathfrak{U}$ and the injectivity of $\rho$ on
  $\mathfrak{K}_1$.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 526, proof of Theorem 1 ("We may assume, changing the order if necessary, that $\rho$ gives an
  isomorphism of $\mathfrak{K}_1$ onto $K$", the map $\rho'$, the definition of $\mathfrak{U}$, "Observe that $\mathfrak{U}$ is an
  ideal of $\mathfrak{T}$", and $\xi_n - \rho'(a_n) \in \mathfrak{U}$).
