# Separable guide potential is a free-space extremum

Let free space have permittivity $\varepsilon_0$, permeability $\mu_0$ and speed of light $c$ (with $c^2 = 1/(\mu_0 \varepsilon_0)$). Let $a : \mathbb{R} \to \mathbb{R}$ and $f : \mathbb{R}^2 \to \mathbb{R}$, $(t, z) \mapsto f(t, z)$, be $C^\infty$, let $k_c \in \mathbb{R}$, and assume the profile equation $a''(x) = -k_c^2\, a(x)$ for all $x$ and the mode equation

$$f_{tt}(t, z) = c^2 \big( f_{zz}(t, z) - k_c^2 f(t, z) \big) \quad \text{for all } t, z.$$

Let $A$ be the separable guide potential with scalar potential $\varphi = 0$ and vector potential $(A_x, A_y, A_z) = (0,\ a(x) f(t, z),\ 0)$. Then:

- the electric and magnetic fields $\mathbf E, \mathbf B$ of $A$ satisfy the source-free vacuum Maxwell equations at speed of light $c$:

    $$\operatorname{div} \mathbf E = 0,\quad \operatorname{div} \mathbf B = 0,\quad \operatorname{curl} \mathbf E = -\partial_t \mathbf B,\quad \operatorname{curl} \mathbf B = \frac{1}{c^2}\, \partial_t \mathbf E.$$

- $A$ is an extremum of the free-space electromagnetic action with zero current density;
- $A$ is $C^\infty$, and the zero current density is $C^\infty$.
