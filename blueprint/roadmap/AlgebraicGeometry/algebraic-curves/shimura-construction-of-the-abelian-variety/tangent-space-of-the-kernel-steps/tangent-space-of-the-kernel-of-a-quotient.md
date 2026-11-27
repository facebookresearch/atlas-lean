# Tangent space of the kernel of a quotient of abelian varieties

Let $B$ be an [abelian variety](../../../abelian-varieties/abelian-scheme.md) over $\mathbb{C}$, $C$ an abelian subvariety of $B$, and
$(A, \nu)$ a [quotient](../../../abelian-varieties/quotient-by-an-abelian-subvariety.md) of $B$ by $C$, so that $C = \mathrm{Ker}(\nu)$. Identify the
tangent space $Y_C$ of $C$ at the origin with its image in $Y_B$ under the differential of the inclusion, and use
the notation of [holomorphic $1$-forms and tangent spaces](../holomorphic-one-forms-steps/holomorphic-one-forms-and-tangent-space.md). Then

$$Y_C = \{ v \in Y_B \mid (u, v)_B = 0 \text{ for all } u \in \delta\nu(D_A) \}.$$

This is Shimura's (1.2), introduced with "We see easily that".

## Depends on

- [Holomorphic $1$-forms and tangent space of a complex abelian variety](../holomorphic-one-forms-steps/holomorphic-one-forms-and-tangent-space.md)
- [Quotient of an abelian variety by an abelian subvariety](../../../abelian-varieties/quotient-by-an-abelian-subvariety.md)

## Proof depends on

- [Holomorphic $1$-forms and tangent space of a complex abelian variety](../holomorphic-one-forms-steps/holomorphic-one-forms-and-tangent-space.md), for (1.1) and the perfect pairing $( \ , \ )_A$
- [Tangent spaces of an abelian subvariety and of the quotient](tangent-spaces-of-an-abelian-subvariety-and-the-quotient.md),
  for $Y_C = \mathrm{Ker}(d\nu)$
- [Quotient of an abelian variety by an abelian subvariety](../../../abelian-varieties/quotient-by-an-abelian-subvariety.md), for $C = \mathrm{Ker}(\nu)$ with $\nu$ surjective

## Proof sketch

For $v \in Y_B$, relation (1.1) gives $(\delta\nu\, u, v)_B = (u, d\nu\, v)_A$ for all $u \in D_A$, and as $( \ , \ )_A$ is
perfect, $v$ is orthogonal to $\delta\nu(D_A)$ if and only if $d\nu\, v = 0$. So the right-hand side of (1.2) is the
kernel of $d\nu$, which is $Y_C$ by the exact sequence $0 \to Y_C \to Y_B \to Y_A \to 0$.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 525, (1.2) and the definition of a quotient just before it.
