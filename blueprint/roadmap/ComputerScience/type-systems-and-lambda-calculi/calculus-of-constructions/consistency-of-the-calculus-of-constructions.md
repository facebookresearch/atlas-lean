# Consistency of the calculus of constructions from normalization

In the calculus of constructions $\lambda C$, written as a [pure type system](../advanced-type-systems/pure-type-systems-and-the-calculus-of.md), there is no term $M$ with $\vdash M : \Pi \alpha{:}{*}.\, \alpha$ in the empty context: the second-order falsum is not inhabited. More precisely, this follows from subject reduction together with weak normalization of typable terms, and both hold for $\lambda C$.

**Proof.** Suppose $\vdash M : \Pi \alpha{:}{*}.\, \alpha$.
- By normalization and subject reduction, $M$ may be taken to be in $\beta$-normal form.
- A closed normal term has no free variable to head an application, and a sort or a product has a sort as its type. So a closed normal term whose type is convertible to a product is an abstraction: $M = \lambda \alpha{:}{*}.\, N$ with $\alpha{:}{*} \vdash N : \alpha$ and $N$ normal.
- The normal term $N$ is a sort, a product, an abstraction, or $x\,N_1 \cdots N_k$ for a variable $x$ of the context.
    - A sort or a product has a sort as its type, and an abstraction has a type convertible to a product. By uniqueness of types up to conversion, none of these can have type $\alpha$.
    - The only variable is $\alpha$, of type $*$, which is not a product. So $k = 0$ and $N = \alpha$, which would have both type $*$ and type $\alpha$, although $* \ne_\beta \alpha$.

## Depends on

- [Pure type systems and the calculus of constructions](../advanced-type-systems/pure-type-systems-and-the-calculus-of.md)

## Background

- [Consistency of CCω](consistency.md): the corresponding statement for the calculus of constructions with universes
- [Subject reduction](subject-reduction.md): subject reduction for the calculus of constructions with universes

## Sources

- H. Barendregt, "Introduction to generalized type systems", *Journal of Functional Programming* 1(2):125–154, 1991, <https://homepages.inf.ed.ac.uk/wadler/papers/barendregt/pure-type-systems.pdf>: Example 3.4(ii) ($\lambda C$), Theorems 2.4–2.6 (subject reduction, strong normalization and uniqueness of types for the $\lambda$-cube), and the second-order falsum $\Pi \alpha{:}{*}.\, \alpha$ in Examples 2.7. The derivation of consistency from these facts is given above.
- T. Coquand and G. Huet, "The calculus of constructions", *Information and Computation* 76(2–3):95–120, 1988.
