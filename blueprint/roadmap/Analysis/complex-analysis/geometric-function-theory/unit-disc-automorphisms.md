# Automorphisms of the open unit disc

Let $\mathbb{D} = \{z \in \mathbb{C} : |z| < 1\}$ be the open unit disc. A map $f\colon \mathbb{D} \to \mathbb{D}$ is an automorphism of $\mathbb{D}$, that is, a bijective holomorphic map of $\mathbb{D}$ onto itself, if and only if there are a real number $\theta$ and a complex number $\alpha$ with $|\alpha| < 1$ such that $f(z) = e^{i\theta}\,\frac{\alpha - z}{1 - \bar\alpha z}$ for all $z \in \mathbb{D}$.

## Proof sketch

For $|\alpha| < 1$, $\psi_\alpha(z) = (\alpha - z)/(1 - \bar\alpha z)$ is holomorphic on $\mathbb{D}$ as a quotient with nonvanishing denominator. The identity $|1 - \bar\alpha z|^2 - |\alpha - z|^2 = (1 - |\alpha|^2)(1 - |z|^2)$ shows that it maps $\mathbb{D}$ into $\mathbb{D}$, and $\psi_\alpha \circ \psi_\alpha$ is the identity, so $\psi_\alpha$ and its rotations are automorphisms. Conversely, given an automorphism $f$, set $\alpha = f^{-1}(0)$ and $g = f \circ \psi_\alpha$; as a composite of holomorphic maps, $g$ is a holomorphic bijection of $\mathbb{D}$ fixing $0$. Its inverse is holomorphic, because the inverse of a bijective holomorphic map is holomorphic. The Schwarz lemma, $|g(z)| \le |z|$, applied to $g$ and to $g^{-1}$ gives $|g(z)| = |z|$. Riemann's removable singularity theorem makes $g(z)/z$ holomorphic on $\mathbb{D}$; it has modulus $1$ throughout, so it is a constant $e^{i\theta}$ by the maximum modulus principle. Hence $f = g \circ \psi_\alpha = e^{i\theta}\psi_\alpha$.

## Expansion

A good expansion of this node links each prerequisite of its proof: the holomorphy of the inverse of a bijective holomorphic map; Riemann's theorem on removable singularities; the Schwarz lemma.

## Depends on

- [Open unit disc](riemann-mapping-theorem/unit-disk.md)

## Proof depends on

- [A holomorphic map into a strictly convex space is constant if its norm attains a maximum on a connected open set](../cauchy-theory/maximum-modulus-principle.md)
- [Chain rule for derivatives of functions of one variable over normed fields](../../calculus-in-normed-spaces/frechet-derivatives/chain-rule-holomorphic.md)

## Sources

- Lars V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill, 1979, Chapter 4, Section 3.4 (Theorem 13, Schwarz's lemma, and Exercise 5).
- Elias M. Stein and Rami Shakarchi, Complex Analysis, Princeton Lectures in Analysis II, Princeton University Press, 2003.
