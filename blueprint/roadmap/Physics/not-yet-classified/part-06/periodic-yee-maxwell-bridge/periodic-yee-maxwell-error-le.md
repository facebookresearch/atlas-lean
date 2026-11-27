# Periodic Yee error bound for a polarized vacuum Maxwell field

Let free space have permittivity $\varepsilon_0 > 0$ and permeability $\mu_0 > 0$, and speed of light $c = 1/\sqrt{\varepsilon_0 \mu_0}$. Let $E_y, H_z : \mathbb{R}^2 \to \mathbb{R}$ be functions of $(t, x)$ such that the field $E = (0, E_y, 0)$, $B = (0, 0, \mu_0 H_z)$ satisfies the source-free vacuum Maxwell equations. Let $N \ge 1$, $h > 0$, $dt > 0$, $L = N h$, and $\rho, T \in \mathbb{R}$ with

$$\frac{c\, dt}{h} \le \rho < 1.$$

Assume $E_y$ and $H_z$ are $L$-periodic in $x$, are $C^3$ in $t$ for each fixed $x$ and $C^3$ in $x$ for each fixed $t$, and their third derivatives are bounded: $|\partial_t^3 E_y| \le M_{Et}$, $|\partial_t^3 H_z| \le M_{Ht}$, $|\partial_x^3 E_y| \le M_{Ex}$, $|\partial_x^3 H_z| \le M_{Hx}$ everywhere. Set

$$M_t = \max(\sqrt{\varepsilon_0}\, M_{Et},\ \sqrt{\mu_0}\, M_{Ht}), \qquad M_x = \max(\sqrt{\varepsilon_0}\, M_{Ex},\ \sqrt{\mu_0}\, M_{Hx}).$$

For grid vectors $E^0, H^0 \in \mathbb{R}^N$, define the periodic Yee iterates by

$$H^{n+1} = H^n - \frac{dt}{\mu_0} D_- E^n, \qquad E^{n+1} = E^n - \frac{dt}{\varepsilon_0} D_+ H^{n+1},$$

with periodic differences $(D_+ v)_j = (v_{j+1} - v_j)/h$ and $(D_- u)_j = (u_j - u_{j-1})/h$. The normalized error at step $n$ is

$$\mathcal{E}_n = \Bigl( h \sum_{j=0}^{N-1} \bigl[ \varepsilon_0 \bigl(E_y(n\,dt, j h) - E^n_j\bigr)^2 + \mu_0 \bigl(H_z(n\,dt - \tfrac{dt}{2}, j h - \tfrac{h}{2}) - H^n_j\bigr)^2 \bigr] \Bigr)^{1/2},$$

and $\mathcal{E}_0$ is the same expression at $n = 0$ (the initial mismatch). Then for every $n \in \mathbb{N}$ with $n\, dt \le T$,

$$\mathcal{E}_n \le \sqrt{\frac{1 + \rho}{1 - \rho}} \left( \mathcal{E}_0 + \frac{T \sqrt{L}\,\bigl(M_t\, dt^2 + c\, M_x\, h^2\bigr)}{6} \right).$$
