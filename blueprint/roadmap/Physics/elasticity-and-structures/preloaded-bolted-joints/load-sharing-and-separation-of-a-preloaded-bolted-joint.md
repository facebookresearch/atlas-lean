# Load sharing and separation of a preloaded bolted joint

This node covers the two-spring model of a preloaded bolted joint. Model the bolt and the clamped members as linear springs of
stiffness $k_b > 0$ and $k_m > 0$ in parallel along the bolt axis, with preload $F_i > 0$, and apply an external tensile load $P \ge 0$ that
separates the members. Let $C = k_b/(k_b + k_m)$ be the joint constant. As long as the members stay in contact, the bolt force and the clamping
force are

$$F_b = F_i + C P, \qquad F_m = F_i - (1 - C) P,$$

and the members stay in contact exactly when $P < P_0 = F_i/(1 - C)$; for $P \ge P_0$ the joint has separated and the bolt carries $F_b = P$.

## Expansion

A good expansion states the compatibility of the bolt and member deformations under the external load, derives the load
sharing, and proves the separation threshold with the contact condition $F_m \ge 0$ as a unilateral constraint. Tolerance propagation and
four-bar linkage classification are separate nodes.

## Sources

- J. E. Shigley and C. R. Mischke, *Mechanical Engineering Design*, 6th edition, McGraw-Hill, 2001, for bolted joints in tension.
