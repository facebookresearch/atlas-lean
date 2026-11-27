# McCann's condition (A1)

An internal-energy density $A$ satisfies McCann's condition in dimension $d$ if $A(0) = 0$ and the
[dilation profile](dilation-profile.md) $\lambda \mapsto \lambda^d A(\lambda^{-d})$ is convex and
nonincreasing on $(0, \infty)$. McCann's Theorem 2.2 shows that under (A1) the internal energy
$U(\rho) = \int A(\rho(x)) \, dx$ is convex along the displacement interpolation between two
absolutely continuous probability measures on $\mathbb{R}^d$. McCann allows $A$ to take the value
$+\infty$; here $A$ is real-valued.

Convexity of the profile is necessary for displacement convexity, since dilations of a uniform
measure are displacement interpolants; McCann's theorem is that it is also sufficient, by a
pointwise argument along the Brenier map using the concavity of
$t \mapsto \det((1-t) I + t \Phi)^{1/d}$ for a nonnegative symmetric matrix $\Phi$ (his Lemma 2.1).

## Sources

- R. J. McCann, *A convexity principle for interacting gases*, Adv. Math. 128 (1997), 153–179, condition (A1), Lemma 2.1 and Theorem 2.2.
