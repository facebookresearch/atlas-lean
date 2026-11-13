# Iterated integral over a polydisc

For $n \in \mathbb{N}$, a function
$u : \mathbb{C}^n \to \mathbb{R}$, a centre $c \in \mathbb{C}^n$ and a radius $R \in \mathbb{R}$,
the iterated polydisc integral $I(u, c, R)$ is defined by recursion on $n$. For $n = 0$ it is
$u(c)$. For $n = m + 1$, writing $c = (c_0, c_1, \dots, c_m)$, it is

$$I(u, c, R) = \int_{|z - c_0| \le R} I\big(u(z, \cdot), (c_1, \dots, c_m), R\big) \, dz,$$

where $u(z, \cdot)$ is the function $y \mapsto u(z, y)$ on $\mathbb{C}^m$ and $dz$ is Lebesgue
measure on $\mathbb{C}$. Thus, for $c = (c_0, \dots, c_{n-1})$ and $D_j$ the closed disc
$|z - c_j| \le R$,

$$I(u, c, R) = \int_{D_0} \cdots \int_{D_{n-1}} u(z_0, \dots, z_{n-1}) \, dz_{n-1} \cdots dz_0.$$

Each integral is a Bochner integral, taken to be $0$ when the integrand is not integrable.
