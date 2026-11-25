# Skorokhod representation on the real line

If distribution functions $F_n$ converge weakly to $F_\infty$, that is, at every continuity point of $F_\infty$,
then there are random variables $Y_n$ on one probability space with distribution functions $F_n$ such that
$Y_n \to Y_\infty$ almost surely.

## Idea

Weak convergence concerns distributions only, while almost sure convergence needs the variables to live
on a common probability space; the theorem builds one. On $(0, 1)$ with Lebesgue measure take $Y_n$ to be the quantile
function of $F_n$, $Y_n(x) = \sup\{y : F_n(y) < x\}$: weak convergence of the $F_n$ makes these functions converge at
all but countably many points. Statements about weak convergence then follow from statements about almost sure
convergence, for example that $E g(X_n) \to E g(X_\infty)$ for bounded continuous $g$. For weakly convergent probability
measures on a Polish space, [the Skorokhod representation theorem](../skorokhod-representation-theorem/skorokhod-representation.md)
gives the same conclusion.

## Statements

- [Skorokhod representation on the real line](skorokhod-representation.md)

## Background

- [Properties of distribution functions](../../distributions/distribution-functions/properties-of-distribution-functions/README.md): distribution functions
- [Inverse transform sampling](../../distributions/distribution-functions/quantile-function-and-inverse-transform-sampling/inverse-transform-sampling/README.md): the quantile function of $F_n$ has distribution function $F_n$, used in the construction
- [Probability measures on the real line from distribution functions](../../foundations/probability-measures-from-distribution-functions/README.md): the probability measure with a given distribution function
