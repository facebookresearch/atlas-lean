# Quotient of an abelian variety by an abelian subvariety

Let $k$ be a field and $B$ an [abelian variety](abelian-scheme.md) over $k$. An **abelian subvariety**
of $B$ (defined over $k$) is a closed subgroup scheme $C$ of $B$ that is itself an abelian variety
over $k$. A **quotient of $B$ by $C$** (over $k$) is a pair $(A, \nu)$ of an abelian variety $A$ over
$k$ and a [homomorphism](homomorphisms-of-abelian-schemes.md) $\nu \colon B \to A$ over $k$ that is
surjective and whose kernel $\nu^{-1}(0_A)$ is $C$.

A quotient $(A, \nu)$ has the universal property of $B / C$: every homomorphism $B \to A'$ of
abelian varieties over $k$ that vanishes on $C$ factors uniquely through $\nu$. In particular two
quotients $(A, \nu)$ and $(A', \nu')$ of $B$ by $C$ are isomorphic by a unique isomorphism
$\varphi \colon A \to A'$ with $\varphi \circ \nu = \nu'$, and $\dim A = \dim B - \dim C$. For every abelian
subvariety $C$ of $B$ defined over $k$ a quotient of $B$ by $C$ over $k$ exists. Shimura's
quotient of $B$ by an abelian subvariety $C$ is such a pair: "a couple $(A, \nu)$ formed by an abelian
variety $A$ which canonically represents $B/C$ and a natural map $\nu \colon B \to A$ with
$C = \mathrm{Ker}(\nu)$ (cf. Chow [3])".

## Depends on

- [Abelian scheme](abelian-scheme.md), for abelian varieties over $k$
- [Homomorphisms of abelian schemes and commutativity](homomorphisms-of-abelian-schemes.md), for
  homomorphisms of abelian varieties

## Proof depends on

This node has no prerequisites.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the existence of the quotient of a group variety by a closed normal subgroup scheme, with its
  universal property, and the fact that the quotient of an abelian variety is an abelian variety
  (Chow's theorem for abelian subvarieties);
- the uniqueness of the quotient up to unique isomorphism and the dimension formula.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 525 (the definition of
  a quotient of $B$ by an abelian subvariety $C$, "cf. Chow [3]").
- W.-L. Chow, *On the quotient variety of an abelian variety*, Proc. Nat. Acad. Sci. U.S.A. 38
  (1952), 1039–1044, as cited in Shimura (1973) above; not read for this page.
