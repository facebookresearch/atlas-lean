# Rigorous QSSA

Let $k_1 > 0$, $k_b \ge 0$, $k_2 > 0$, $s_0 > 0$ and $T > 0$, let $K_M = (k_b + k_2)/k_1$, and let
$\bar S \colon \mathbb{R} \to \mathbb{R}$ solve the reduced equation

$$\frac{d\bar S}{d\tau} = -\frac{k_2 \bar S}{K_M + \bar S} \quad (\tau \ge 0), \qquad \bar S(0) = s_0.$$

Then there is a constant $C$ such that for every $e_0 \in (0, 1]$ and every
[solution](is-solution.md) $(s, c, e, p)$ of the Michaelis–Menten system with $s(0) = s_0$,
$c(0) = 0$ and $e(0) = e_0$, the substrate on the slow time scale $\tau = e_0 t$ satisfies
$|s(\tau/e_0) - \bar S(\tau)| \le C e_0$ for all $\tau \in [0, T]$ (Tikhonov 1952;
Heineken–Tsuchiya–Aris 1967).
