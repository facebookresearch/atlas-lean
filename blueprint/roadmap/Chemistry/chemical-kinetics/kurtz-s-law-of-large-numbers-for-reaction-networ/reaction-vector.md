# Reaction vector of a reaction

Let $G$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
species set $S$ and reaction set $\rho$. The reaction vector of a reaction $r$ is the real vector
$\zeta_r \in \mathbb{R}^S$ with components

$$\zeta_r(i) = \mathrm{prod}(r)_i - \mathrm{src}(r)_i \qquad (i \in S),$$

the net change in the count of species $i$ when $r$ fires once. The subtraction is in the real
numbers, so a component is negative when $r$ consumes more of species $i$ than it produces.
