# Decomposition of the Hecke algebra of the modular Jacobian

Let $\mathfrak{T}$ be the [Hecke algebra](hecke-algebra-of-the-modular-jacobian.md) of the Jacobian $J$ of the modular
curve of a group $\Gamma$ of level $N$, and $\mathfrak{R}$ its radical. Then $\mathfrak{T}$ is finite-dimensional over
$\mathbb{Q}$, and

$$\mathfrak{T} = \mathfrak{R} \oplus \mathfrak{S}$$

as $\mathbb{Q}$-vector spaces, for a commutative semisimple $\mathbb{Q}$-subalgebra $\mathfrak{S}$ of $\mathfrak{T}$. Writing
$\mathfrak{K}_1, \dots, \mathfrak{K}_r$ for the simple components of $\mathfrak{S}$, so that
$\mathfrak{S} = \mathfrak{K}_1 \oplus \dots \oplus \mathfrak{K}_r$, each $\mathfrak{K}_i$, a commutative simple algebra, is a field.

Shimura states the decomposition at the start of the proof of Theorem 1, with no further argument; the finite
dimensionality, implicit there, comes from that of $\mathrm{End}(J) \otimes \mathbb{Q}$.

## Depends on

- [Hecke algebra of the Jacobian of a modular curve](hecke-algebra-of-the-modular-jacobian.md)

## Proof depends on

- [Hecke algebra of the Jacobian of a modular curve](hecke-algebra-of-the-modular-jacobian.md)
- [Hecke operators on cusp forms and Hecke endomorphisms of the Jacobian](hecke-operators-and-hecke-endomorphisms-under-mu.md), for the comparison of the $\xi_n$ with the $T_n$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the finite dimensionality of $\mathrm{End}(J) \otimes \mathbb{Q}$ over $\mathbb{Q}$, hence of $\mathfrak{T}$;
- the principal theorem of Wedderburn (Malcev) for finite-dimensional algebras over a field of characteristic zero:
  a semisimple subalgebra complementary to the radical;
- the commutativity of $\mathfrak{T}$, from which that of $\mathfrak{S}$ follows: the $T_n$ commute on $S_2(\Gamma)$, and
  $\mu \circ T_n = \delta\xi_n \circ \mu$ together with the injectivity of $\alpha \mapsto \delta\alpha$ on
  $\mathrm{End}(J) \otimes \mathbb{Q}$ carries this to the $\xi_n$;
- the structure of a finite-dimensional commutative semisimple algebra as a finite product of fields, its simple
  components.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 526, proof of Theorem 1 ($\mathfrak{T} = \mathfrak{R} \oplus \mathfrak{S}$, with $\mathfrak{S}$ commutative
  semisimple and simple components $\mathfrak{K}_1, \cdots, \mathfrak{K}_r$).
