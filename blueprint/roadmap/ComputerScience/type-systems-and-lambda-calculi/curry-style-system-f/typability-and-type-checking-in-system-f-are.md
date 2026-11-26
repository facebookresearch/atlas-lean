# Typability and type checking in System F are undecidable

In [Curry-style System F](curry-style-system-f.md):

1. typability many-one reduces to type checking: $M$ is typable if and only if $\emptyset \vdash K\, I\, (\lambda x_1 \dots x_n.\, M) : \forall a.\, a \to a$, where
   $x_1, \dots, x_n$ are the free variables of $M$, $K = \lambda x y.\, x$ and $I = \lambda x.\, x$;
2. left-uniform two-inequality semi-unification many-one reduces to typability;
3. hence typability and type checking are both undecidable (Wells), and they are recursively equivalent.

## Depends on

- [Curry-style System F](curry-style-system-f.md)
- [Two-inequality semi-unification](two-inequality-semi-unification.md)

## Proof depends on

- [Semi-unification is undecidable](semi-unification-is-undecidable.md)

## Sources

- A. Dudenhefner, "The undecidability of System F typability and type checking for reductionists", *Proceedings of the 36th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS)*, 2021, <https://ps.uni-saarland.de/Publications/documents/Dudenhefner_2021_SystemF.pdf>: Lemma 29 (prenex simulation), Lemma 40 (reduction from left-uniform semi-unification to typability), Corollary 41 (undecidability of typability), Lemma 42 (reduction from typability to type checking) and Corollary 43 (undecidability of type checking).
- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Theorem 12.5.7 (Wells: type reconstruction and type checking are recursively equivalent and undecidable).
