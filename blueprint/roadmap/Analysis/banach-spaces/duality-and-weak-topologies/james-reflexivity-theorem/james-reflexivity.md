# James' reflexivity theorem

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $E$ be a
Banach space over $\mathbb{K}$. The canonical embedding of $E$ into its bidual $E^{**}$ is
surjective if and only if every continuous linear functional $f \colon E \to \mathbb{K}$ attains
its norm on the closed unit ball, that is, there is $x \in E$ with $\|x\| \le 1$ and
$|f(x)| = \|f\|$.

Proof: The reverse implication uses the general real James convex-block argument, with Goldstine
approximation and weak-star cluster hulls. Restriction of scalars transfers the result from real
scalars to $\mathbb{K}$.

## Sources

- R. C. James, Reflexivity and the Supremum of Linear Functionals, Ann. of Math. 66 (1957), DOI 10.2307/1970122; Bourbaki form; Lean states `RCLike` Banach case with norm-attainment equivalence for reflexivity.
