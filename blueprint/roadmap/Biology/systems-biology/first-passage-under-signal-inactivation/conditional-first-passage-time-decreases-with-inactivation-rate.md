# Conditional first passage time decreases with the inactivation rate

A signaling molecule is activated at the cell membrane and diffuses through the cytosol $\mathcal{C}$ (reflecting cell membrane and organelle surfaces, absorbing nuclear membrane $\partial\mathcal{N}$) while being inactivated at rate $\lambda \geq 0$. Its density of still-active molecules solves

$$\partial_t p_\lambda = D\Delta p_\lambda - \lambda p_\lambda \ \text{ in } \mathcal{C}, \qquad p_\lambda = 0 \text{ on } \partial\mathcal{N}, \qquad \nabla p_\lambda\cdot\eta = 0 \text{ on reflecting surfaces},$$

so $p_\lambda = e^{-\lambda t}p_0$ and the arrival-time density at the nucleus is $f_\lambda(t) = e^{-\lambda t}f(t)$, where $f$ is the first passage density without inactivation. Let $T_\lambda$ be the arrival time ($T_\lambda = \infty$ if the molecule is inactivated first),

$$Z_\lambda = \Pr[T_\lambda < \infty] = \int_0^\infty e^{-\lambda t}f(t)\,dt, \qquad F_\lambda(t) = \Pr[T_\lambda < t \mid T_\lambda < \infty] = \frac{\int_0^t e^{-\lambda s}f(s)\,ds}{Z_\lambda} .$$

**Theorem.** For every fixed $t > 0$, $Z_\lambda$ is strictly decreasing and $F_\lambda(t)$ is strictly increasing in $\lambda \geq 0$.

**Corollary.** The conditional mean first passage time $\langle T_\lambda\rangle = \mathbb{E}[T_\lambda \mid T_\lambda < \infty] = -\frac{d}{d\lambda}\log Z_\lambda$ and the conditional median $F_\lambda^{-1}(1/2)$ are strictly decreasing in $\lambda$.

Stronger inactivation thus delivers fewer molecules but faster and more tightly timed ones: it filters out molecules that took long diffusive paths. If the number of molecules reaching the nucleus is held fixed by activating $N_0 \propto 1/Z_\lambda$ molecules, the arrival signal sharpens and moves earlier as $\lambda$ grows, at the cost of activating many more molecules. The same statements hold for the voxel (semi-discrete) version of the model on reconstructed cell geometries.

## Expansion

$\frac{d}{d\lambda}Z_\lambda = -\int_0^\infty t e^{-\lambda t}f(t)\,dt < 0$ because the diffusion first passage density is positive for all $t > 0$. For the conditional CDF, $\frac{\partial}{\partial\lambda}\log F_\lambda(t) = \mathbb{E}[T_\lambda \mid T_\lambda < \infty] - \mathbb{E}[T_\lambda \mid T_\lambda < t] > 0$, since conditioning on arriving before $t$ strictly lowers the mean when $f$ has mass on both sides of $t$. Monotonicity of $F_\lambda(t)$ for every $t$ is stochastic ordering of the conditional laws, which gives the monotonicity of the conditional mean, median and every other quantile. The identity $\langle T_\lambda\rangle = -\partial_\lambda\log Z_\lambda$ is the Laplace-transform derivative.

## Sources

- J. Ma, M. Do, M. A. Le Gros, C. S. Peskin, C. A. Larabell, Y. Mori, S. A. Isaacson, "Strong intracellular signal inactivation produces sharper and more robust signaling from cell membrane to nucleus", *PLoS Computational Biology* 16(11) (2020) e1008356. Results, "Signal inactivation" (Eqs. 7–9, 10–12), Theorem 1 and Corollary 1 (proved in S1 Text, Section SI1), and Eqs. 13–14 for the fixed-signal comparison. <https://doi.org/10.1371/journal.pcbi.1008356>. PMCID: PMC7704053.
