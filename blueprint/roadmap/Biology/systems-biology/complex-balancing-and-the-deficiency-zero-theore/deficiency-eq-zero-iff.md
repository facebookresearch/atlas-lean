# Deficiency zero in linear form

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
species set $S$ and finite reaction set $\rho$. Its
[deficiency](../../../Dynamics/smooth-dynamics/deficiency.md) is $\delta = 0$ if and only if,
whenever $\alpha \in \mathbb{R}^\rho$ satisfies
$\sum_{r} \alpha_r (\mathrm{prod}(r) - \mathrm{src}(r)) = 0$ in $\mathbb{R}^S$, every function
$\eta \colon \mathbb{N}^S \to \mathbb{R}$ satisfies

$$\sum_{r \in \rho} \alpha_r \bigl(\eta(\mathrm{prod}(r)) - \eta(\mathrm{src}(r))\bigr) = 0.$$

With $C$ the set of [complexes](../../../Dynamics/smooth-dynamics/complexes.md) of $N$, let
$\partial \colon \mathbb{R}^\rho \to \mathbb{R}^C$ send $\alpha$ to
$\sum_r \alpha_r (e_{\mathrm{prod}(r)} - e_{\mathrm{src}(r)})$ and let
$Y \colon \mathbb{R}^C \to \mathbb{R}^S$ be the linear map with $Y(e_y) = y$. Then
$Y(\partial \alpha) = \sum_r \alpha_r (\mathrm{prod}(r) - \mathrm{src}(r))$, the left side of the
display is $\sum_{y \in C} \eta(y)\, (\partial \alpha)_y$, and the condition says
$\ker Y \cap \operatorname{im} \partial = \{0\}$. The equivalence is the
[deficiency zero criterion for indexed complexes](card-sub-card-sub-finrank-eq-zero-iff.md) applied
to the complexes of $N$. The condition is the form of the deficiency hypothesis used for
[positive balancing weights](exists-pos-is-complex-balanced-of-balanc.md) and for the
[existence of complex-balanced states](exists-pos-is-complex-balanced-of-defici.md).

## Sources

- M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019), Theorem 6.4.7.
