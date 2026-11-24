# Constant of the reversible slow-window substrate estimate

For real $k_1, k_{-1}, k_2, k_{-2}$, total mass $M$ and $T$, the constant of the substrate estimate
on the slow window $[0, T]$ is

$$
C(T) = (k_1 M + k_{-1}) \Bigl(\frac{1}{k_{-1} + k_2} +
\Bigl(\frac{F}{(k_{-1} + k_2)^2} + \frac{k_{-2}}{k_{-1} + k_2}\Bigr) T\Bigr),
$$

with the [forcing constant](complex-forcing-const.md) $F$ and quotients by $0$ read as $0$. When
$k_{-1} + k_2 = 0$ all three quotients are $0$ and $C(T) = 0$ for every $T$. It is affine in $T$,
and nondecreasing in $T$ when $k_1, k_{-1}, k_{-2}, M \ge 0$ and $k_2 > 0$.
