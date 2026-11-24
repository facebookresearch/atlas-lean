# Identifiability of a linear calibration model $y = A\theta$

For a real $m \times n$ matrix $A$, the linear calibration model $y = A\theta$, with parameters
$\theta \in \mathbb{R}^n$ and observations $y \in \mathbb{R}^m$, is identifiable when the map
$\theta \mapsto A\theta$ is injective: $A\theta_1 = A\theta_2$ implies $\theta_1 = \theta_2$.

This is a property of the matrix alone (linear-algebraic identifiability); no noise model or
probability distribution is involved. It holds exactly when the kernel of $A$ is trivial
([kernel criterion](identifiable-iff-trivial-ker.md)). Without it no observation determines its
parameter: a nonzero kernel vector gives every parameter a
[distinct parameter with the same observation](exists-distinct-of-nontrivial-ker.md), so a
unique estimate of $\theta$ from $y$ requires identifiability.
