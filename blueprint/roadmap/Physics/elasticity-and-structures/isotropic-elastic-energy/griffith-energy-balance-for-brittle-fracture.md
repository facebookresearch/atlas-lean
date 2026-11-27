# Griffith energy balance for brittle fracture

Consider a linear elastic plate of unit thickness with Young's modulus $E > 0$ and surface energy $\gamma > 0$ per unit area. It contains a crack of length $a > 0$ and is loaded by a remote tensile stress $\sigma$ normal to the crack, in plane stress. In Griffith's energy model, opening the crack releases the strain energy $U(a) = -\pi\sigma^2 a^2/(2E)$, and creating its two faces costs the surface energy $S(a) = 2\gamma a$.

**Theorem (Griffith).**
1. For fixed $\sigma \ne 0$, the total energy $\Pi(a) = S(a) + U(a)$ is a concave quadratic in $a$. It is maximized at the critical length

    $$
    a_c = \frac{2E\gamma}{\pi\sigma^2}.
    $$

    For $a < a_c$, a small extension raises $\Pi$, and for $a \ge a_c$ every extension lowers $\Pi$.
2. Equivalently, for a fixed crack length $a$ and a tensile stress $\sigma > 0$, crack growth lowers the energy exactly when $\sigma$ is at least the *fracture stress*

    $$
    \sigma_f = \sqrt{\frac{2E\gamma}{\pi a}}.
    $$

3. In terms of the *strain energy release rate* $G = -dU/da = \pi\sigma^2 a/E$, the criterion reads $G \ge 2\gamma$. Irwin and Orowan replaced $2\gamma$ by a measured critical value $G_c$ that also includes plastic dissipation.

**Proof.** $\Pi'(a) = 2\gamma - \pi\sigma^2 a/E$ is decreasing in $a$ and vanishes exactly at $a = a_c$; since $\Pi$ is strictly concave, every extension from $a \ge a_c$ lowers it. Solving $\Pi'(a) = 0$ for $\sigma$ gives $\sigma_f$, and $-U'(a) = \pi\sigma^2 a/E$.

The criterion concerns a single crack in a homogeneous brittle solid. Damage in composites, meaning matrix cracking, delamination and fiber failure under rate- and history-dependent laws, needs damage-evolution laws and homogenization error bounds beyond this energy balance.

## Sources

- D. Roylance, *Introduction to Fracture Mechanics*, course module, Department of Materials Science and Engineering, MIT, 2001, <http://web.mit.edu/course/3/3.11/www/modules/frac.pdf>, Introduction (the fracture energy balance) and "The stress intensity approach":
    - the strain energy density $\sigma^2/(2E)$ and the unloaded triangular regions with $\beta = \pi$ in plane stress, giving $U = -(\sigma^2/2E)\,\pi a^2$;
    - the surface energy $S = 2\gamma a$, and the condition $\partial(S + U)/\partial a = 0$ giving $\sigma_f = \sqrt{2E\gamma/(\pi a)}$;
    - Irwin and Orowan's critical strain energy release rate $G_c$, and the stress intensity factor $K_I = \sigma\sqrt{\pi a}$.
