# Solution of the Iris domain equation

The Iris type of propositions exists: when uniform predicates over a ghost-state functor form a locally contractive bifunctor, there is a complete OFE of propositions isomorphic to the uniform predicates over the ghost state built from it.

**Theorem.** Let $F$ assign to each OFE a unital camera such that $G(T) \triangleq \mathrm{UPred}(F(T))$ is a locally contractive bifunctor $\mathbf{COFE}^{op} \times \mathbf{COFE} \to \mathbf{COFE}$. Then there is a COFE $\mathit{iProp}$, unique up to isomorphism, with

$$
\mathit{iProp} \cong \mathrm{UPred}(\mathit{Res}), \qquad \mathit{Res} \triangleq F(\mathit{iProp}).
$$

## Depends on

- [America-Rutten theorem](../step-indexed-foundations/america-rutten-theorem.md)
- [Uniform predicates](uniform-predicates.md)
- [Cameras](../cameras/cameras.md)

## Proof depends on

- [America-Rutten theorem](../step-indexed-foundations/america-rutten-theorem.md)
- [Uniform predicates](uniform-predicates.md)

## Expansion

This is the America-Rutten theorem applied to $G$; $G(1, 1)$ is inhabited because every $\mathrm{UPred}(M)$ contains the predicate true everywhere. The source makes the notation $G(T)$ precise as a bifunctor by composing $F$ with $\mathrm{UPred}$, and shows local contractiveness by composing locally non-expansive constructions (UPred, agreement, function spaces) with the locally contractive later functor. At user level the source states, informally, that it suffices for $F$ to be built from the usual type constructors, fixed OFEs and cameras and the camera constructions of the model, with every recursive occurrence of its argument guarded by the later OFE, and that a family $(F_i)$ can be combined as $F(X) = \prod_i \mathbb{N} \xrightarrow{fin} F_i(X)$. Without step-indexing the analogous set-theoretic equation $\mathit{iProp} = \mathrm{AG}_0(\mathit{iProp}) \xrightarrow{mon} \mathit{Prop}$ has no solution, by a cardinality argument the source mentions at the start of its Section 4.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 4.6 (the equation IRIS, G(T) = UPred(F(T)), its local contractiveness, the category of cameras) and Section 4.7 (informal sufficient conditions and the global functor); Section 4 opening (PRE-IRIS has no solution for AG0).
