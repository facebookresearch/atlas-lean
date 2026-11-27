# QSSA contract for the Michaelis–Menten system

For real $k_1, k_b, k_2, s_0$ and $T$, the QSSA contract is the following proposition. If $k_1 > 0$,
$k_b \ge 0$, $k_2 > 0$ and $s_0 > 0$, then for every
[solution of the reduced problem](is-reduced-solution-on.md) $u$ on $[0, T]$ and every
$\delta \in (0, T]$ there is a constant $C$ such that, for every $e_0 > 0$ and every
[solution](is-solution-on.md) $(s, c)$ with total enzyme $e_0$ on the window $[0, t_S T]$ with
$s(0) = s_0$ and $c(0) = 0$,

- $|s(t_S \theta)/s_0 - u(\theta)| \le C \varepsilon$ for every $\theta \in [0, T]$, and
- $|c(t_S \theta)/e_0 - h(u(\theta))| \le C \varepsilon$ for every $\theta \in [\delta, T]$,

with the [slow time scale](slow-time-scale.md) $t_S = (s_0 + K_M)/(k_2 e_0)$, the
[Segel–Slemrod parameter](qssa-epsilon.md) $\varepsilon = e_0/(s_0 + K_M)$, the
[slow manifold](slow-manifold.md) $h(x) = x/(\kappa + x)$ and $\kappa = K_M/s_0$. The constant may
depend on $k_1, k_b, k_2, s_0, T, \delta$ and $u$, but not on $e_0$. The complex clause excludes the
initial layer $\theta < \delta$: at $\theta = 0$ the complex error is $1/(1 + \kappa)$ for every
$e_0$, so a bound $C \varepsilon$ below that value [fails there](not-complex-le-at-zero.md). For
other parameter values the contract holds vacuously, and for $T \le 0$ there is no $\delta$, so it
holds and gives no bound (Tikhonov 1952, Vasil'eva 1963, Heineken, Tsuchiya and Aris 1967, Segel and
Slemrod 1989).
