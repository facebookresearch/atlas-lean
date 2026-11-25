# Net radiative power is emission minus absorption

A *black enclosure* on a finite set of surfaces $i$ is a pair of areas $A_i$ and view factors $F_{ij}$ with $A_i > 0$, $F_{ij} \ge 0$, $\sum_j F_{ij} = 1$ for every $i$, and reciprocity $A_i F_{ij} = A_j F_{ji}$ for all $i, j$. For a constant $\sigma > 0$ and temperatures $T_i \ge 0$, the net power leaving surface $i$ is $P_i = \sum_j A_i F_{ij} \sigma (T_i^4 - T_j^4)$. Writing

$$\Phi(T) = \int_0^{\pi/2} \frac{\sigma T^4}{\pi} \cos\theta \,(2\pi \sin\theta)\, d\theta$$

for the hemispheric integral of the Lambertian intensity $\sigma T^4/\pi$, every surface $i$ satisfies

$$P_i = A_i\, \Phi(T_i) - \sum_j A_j F_{ji}\, \Phi(T_j).$$
