# Evanescent TE10 field below cutoff

Let $k_c = \pi/a$ and $\kappa = \sqrt{k_c^2 - \omega^2/c^2}$. The evanescent TE10 fields are

$$E = \bigl(0,\; E_0 \sin(k_c x)\, e^{-\kappa z} \cos(\omega t),\; 0\bigr),$$

$$B = \Bigl(-\tfrac{\kappa E_0}{\omega} \sin(k_c x)\, e^{-\kappa z} \sin(\omega t),\; 0,\; -\tfrac{k_c E_0}{\omega} \cos(k_c x)\, e^{-\kappa z} \sin(\omega t)\Bigr).$$

Fields $E, B$ of $(t, x, y, z)$ satisfy the *source-free vacuum Maxwell equations* at speed $c > 0$ if, at every time and point, $\nabla \cdot E = 0$, $\nabla \cdot B = 0$, $\nabla \times E = -\partial_t B$ and $\nabla \times B = c^{-2} \partial_t E$.

Let $c > 0$ be the speed of light, $a > 0$, $b > 0$, $E_0 \ne 0$ and $0 < \omega < c\, k_c$. Then $\kappa > 0$ and $\kappa^2 = k_c^2 - \omega^2/c^2$; the fields satisfy the source-free vacuum Maxwell equations; at every time they satisfy the PEC conditions on the four side walls of the guide of widths $a, b$; $E$ is not identically zero; and for all $t, x, y$, every $z \ge 0$ and every component $i$,

$$|E_i| \le |E_0|\, e^{-\kappa z}, \qquad |B_i| \le \frac{(\kappa + k_c)\, |E_0|}{\omega}\, e^{-\kappa z}.$$
