# Tangent space of the kernel of a quotient of abelian varieties

Let $B$ be an [abelian variety](../../abelian-varieties/abelian-scheme.md) over $\mathbb{C}$, $C$ an abelian subvariety of $B$, and
$(A, \nu)$ a [quotient](../../abelian-varieties/quotient-by-an-abelian-subvariety.md) of $B$ by $C$, so that $C = \mathrm{Ker}(\nu)$. Identify the
tangent space $Y_C$ of $C$ at the origin with its image in $Y_B$ under the differential of the inclusion, and use
the notation of [holomorphic $1$-forms and tangent spaces](holomorphic-one-forms-and-tangent-space.md). Then

$$Y_C = \{ v \in Y_B \mid (u, v)_B = 0 \text{ for all } u \in \delta\nu(D_A) \}.$$

This is Shimura's (1.2), introduced with "We see easily that".

## Depends on

- [Holomorphic $1$-forms and tangent space of a complex abelian variety](holomorphic-one-forms-and-tangent-space.md)
- [Quotient of an abelian variety by an abelian subvariety](../../abelian-varieties/quotient-by-an-abelian-subvariety.md)

## Proof depends on

- [Holomorphic $1$-forms and tangent space of a complex abelian variety](holomorphic-one-forms-and-tangent-space.md), for (1.1) and the perfect pairing
- [Quotient of an abelian variety by an abelian subvariety](../../abelian-varieties/quotient-by-an-abelian-subvariety.md), for $C = \mathrm{Ker}(\nu)$ with $\nu$ surjective

## Expansion

This node is still to be broken down. A good expansion states and links:

- the exact sequence $0 \to Y_C \to Y_B \to Y_A \to 0$, the second map being $d\nu$: the kernel of $d\nu$ is the
  tangent space of $\mathrm{Ker}(\nu) = C$, an abelian subvariety, and $d\nu$ is surjective because $\nu$ is;
- the identification, by (1.1) and the perfectness of the pairings, of the annihilator of $\delta\nu(D_A)$ in $Y_B$
  with the kernel of $d\nu$.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 525, (1.2) and the definition of a quotient just before it.
