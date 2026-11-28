# Weak and strong branches of the attached oblique shock

This node covers the following result for a calorically perfect gas with ratio of specific heats $\gamma > 1$. Let a uniform
upstream flow have Mach number $M_1 > 1$, and let a straight shock make the wave angle $\beta$ with the upstream velocity, where
$\arcsin(1/M_1) < \beta \le \pi/2$. Applying the normal-shock jump relations to the normal component $M_1 \sin\beta$ and keeping the
tangential velocity continuous, the flow turns through the deflection angle $\theta \in [0, \pi/2)$ given by

$$\tan\theta = 2\cot\beta\,\frac{M_1^2\sin^2\beta - 1}{M_1^2(\gamma + \cos 2\beta) + 2}.$$

For each $M_1 > 1$ there is a maximum deflection $\theta_{\max}(M_1) \in (0, \pi/2)$ such that for $0 < \theta < \theta_{\max}(M_1)$ exactly
two wave angles give the deflection $\theta$ (the weak and the strong branch), exactly one does at $\theta = \theta_{\max}(M_1)$, and none does
for $\theta > \theta_{\max}(M_1)$. Both branches increase the entropy, as the normal shock does for a normal Mach number above one.

## Expansion

A good expansion first states the oblique-shock geometry and the reduction to the normal-shock relations with continuous
tangential velocity, then proves the displayed deflection formula, and then the branch count by studying $\beta \mapsto \theta$ on
$(\arcsin(1/M_1), \pi/2]$: it vanishes at both ends and has a single interior maximum. The Prandtl-Meyer relation for isentropic
expansion fans, $\nu(M) = \sqrt{\tfrac{\gamma+1}{\gamma-1}}\arctan\sqrt{\tfrac{\gamma-1}{\gamma+1}(M^2-1)} - \arctan\sqrt{M^2-1}$, is a separate
node.

## Sources

- J. D. Anderson, *Fundamentals of Aerodynamics*, 3rd edition, McGraw-Hill, 2001, for the oblique-shock and expansion-wave relations.
