# Regular level sets are locally parametrized by immersions

Let
$f \colon \mathbb{R}^{k+m} \to \mathbb{R}^m$ be a $C^1$ map and let $x_0 \in \mathbb{R}^{k+m}$ be a
point at which the derivative $Df(x_0)$ is surjective. Then there exist an open set
$U \subseteq \mathbb{R}^k$, a point $u_0 \in U$, a map $\varphi \colon \mathbb{R}^k \to
\mathbb{R}^{k+m}$ that is $C^1$ and a $C^1$ immersion on all of $\mathbb{R}^k$, and a
neighbourhood $V$ of $x_0$ such that $\varphi(u_0) = x_0$ and
$\varphi(U \cap \varphi^{-1}(V)) = V \cap f^{-1}(f(x_0))$.

Proof: Apply the implicit function theorem in adapted linear coordinates, then use a smooth bump
to extend the local graphing function globally. A shear chart makes its graph map an immersion.

## Sources

- undergrad.yaml `Submanifolds of R^n / local parameterization` (missing); J. Lee, Introduction to Smooth Manifolds, 2nd ed., Ch. 4 (rank theorem).
