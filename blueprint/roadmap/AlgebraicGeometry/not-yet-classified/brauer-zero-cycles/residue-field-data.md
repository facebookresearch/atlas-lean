# Residue Field Data

Data for transferring Brauer classes from the residue field $\kappa(x)$ of a dimension-zero
point $x$ of $X$ to $k$: a $k$-embedding `embedding` of $\kappa(x)$ into the separable closure of
$k$; a `FiniteFieldPair` for it, which identifies the separable closures and, compatibly with their
actions, the absolute Galois group of $\kappa(x)$ with the subgroup of that of $k$ fixing the image,
this subgroup being open of finite index; and a corestriction
$\mathrm{Br}(\kappa(x)) \to \mathrm{Br}(k)$ given on cocycle classes by the transfer formula
(`NormalizedCorestriction`).
