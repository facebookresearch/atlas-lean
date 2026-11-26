# Periodic complex Riccati equation and its Möbius Poincaré map

Let $c_0, c_1, c_2$ be continuous $2\pi$-periodic complex functions, and consider

$$
\frac{dz}{dt} = c_0(t) + c_1(t) z + c_2(t) z^2 .
$$

**Proposition 2.** Suppose there is $c_* > 0$ such that

$$
\operatorname{Re}\big(\overline{c_0(t)}\, z + c_1(t) + c_2(t) z\big) \le -c_* \operatorname{Re}(z + 1)
\qquad \text{for all } z \in \overline{\mathbb{D}},\ t \in [0, 2\pi],
$$

and that $z = -1$ is not a fixed point of the equation. Then the period-$2\pi$ Poincaré map is a hyperbolic or loxodromic Möbius transformation. Its stable fixed point lies in the open unit disc $\mathbb{D}$, and its unstable fixed point lies in $\widehat{\mathbb{C}} \setminus \overline{\mathbb{D}}$. Hence the equation has exactly one stable $2\pi$-periodic solution, and it satisfies $|z(t)| < 1$ for all $t$. By Remark 1, this solution is asymptotically stable.

**Application to theta-neuron fields (Remark 2).** After rescaling time by the frequency $\omega > 0$, the Ott–Antonsen field equation at each fixed position $x$ is this Riccati equation with

$$
c_0 = c_2 = i\Big(W + \zeta - \frac{1}{2\omega}\Big), \qquad c_1 = 2i\Big(W + \zeta + \frac{1}{2\omega}\Big), \qquad \zeta = \frac{\eta_0 + i\gamma}{2\omega},
$$

where $W(x,t) = \tfrac{\kappa}{2\omega}(K * H_n(u))$ is real and $2\pi$-periodic. Then $\operatorname{Re}(\bar c_0 z + c_1 + c_2 z) = -\tfrac{\gamma}{\omega}\operatorname{Re}(z+1)$ and $c_0 - c_1 + c_2 = -2i/\omega \neq 0$. So for every real periodic input $W$ and every $\gamma > 0$ there is a unique stable periodic local order parameter inside the disc.

## Depends on

- [Theta-neuron ring network and its Ott–Antonsen neural field](theta-neuron-ring-network-and-its-ott-antonsen-neural-field.md)

## Expansion

The flow of a Riccati equation acts by Möbius transformations, which is classical. Suppose the period map sent a point of the unit circle back to the unit circle. Solutions starting in $\overline{\mathbb{D}}$ stay there. On the unit circle, $\tfrac{d}{dt}|z|^2 = 2\operatorname{Re}(\bar c_0 z + c_1 + c_2 z) \le -2c_*\operatorname{Re}(z+1)$, and this is negative away from $z = -1$. Combined with the mean value theorem, this contradicts $|z(2\pi)| = 1$. So the map sends $\overline{\mathbb{D}}$ strictly into $\mathbb{D}$. A Möbius map with that property has one attracting fixed point inside the disc and its repelling partner outside. In practice the Möbius map is reconstructed from three numerical solutions with initial values in $\mathbb{D}$. Its fixed point inside the disc is found by solving a quadratic, and a fourth solve gives the periodic orbit, with no Newton iteration in time.

## Sources

- Laing CR, Omel'chenko OE. Periodic solutions in next generation neural field models. *Biological Cybernetics* 117 (2023) 259–274. <https://doi.org/10.1007/s00422-023-00969-6>. PMCID: PMC10600056.
