# Effective stress level and characteristic stress for evolutionary rescue

Work in the setting of [evolutionary rescue rates in Fisher's geometric model](evolutionary-rescue-rates-in-fisher-s-geometric-model.md): a clonal population of size $N_0$, growth rate $r(z) = r_{\max} - \lVert z\rVert^2/2$ in the new environment, ancestral decay rate $r_D > 0$, mutation rate $U$ and isotropic Gaussian mutation effects of variance $\lambda$ per trait in $n$ dimensions, in the strong-selection weak-mutation regime, with reproductive variance $\sigma = 1$. Define

$$\psi_D = 2\Big(\sqrt{1 + r_D/r_{\max}} - 1\Big), \qquad \alpha = \frac{\psi_D^2\, r_{\max}}{4\lambda} .$$

**Small-mutation-effect limit.** If $4U/n^2 < \lambda \ll r_{\max}$, the de novo rescue rate satisfies

$$\omega_{DN} \approx \omega_{DN}^{*} = U\,\frac{(1 + \psi_D/2)^{(1-n)/2}}{1 + \psi_D/4}\, g(\alpha), \qquad g(\alpha) = \frac{e^{-\alpha}}{\sqrt{\pi\alpha}} - \operatorname{erfc}(\sqrt{\alpha}),$$

and under mild stress ($\psi_D/2 \to 0$) $\omega_{DN}^{*} \to U\,g(\alpha)$, so $P_R \approx 1 - \exp(-N_0 U g(\alpha))$. The function $g$ is strictly decreasing, so rescue becomes less likely with a larger decay rate $r_D$, a lower peak $r_{\max}$ or a smaller mutational variance $\lambda$; all of these act through the single **effective stress level** $\alpha$, and at mild stress the dependence on dimensionality $n$ disappears.

**Characteristic stress.** For $\alpha \gg 1$, $g(\alpha) \approx \alpha^{-3/2}e^{-\alpha}/(2\sqrt{\pi})$. The stress level at which $P_R = 1/2$ is

$$\alpha_c = g^{-1}\!\Big(\frac{\log 2}{N_0 U}\Big) \approx 0.9\,\log(N_0 U) - 2.7 \qquad (N_0 U \gg 1).$$

Since $\alpha_c \propto (r_D^{c})^2$, the decay rate $r_D^{c}$ that a population survives half of the time grows only like $\sqrt{\log(N_0 U)}$ for large $N_0 U$, whereas a context-independent model with a fixed proportion $q_R$ of rescue mutations gives $r_D^{c} = q_R N_0 U/\log 2$, linear in $N_0 U$. Rescue probability therefore drops sharply over a narrow window of stress.

## Proof sketch

A mutant of $z_A$ is resistant when it lands inside the ball $\lVert z\rVert^2 < 2r_{\max}$. The shortest jump that does so has length $\lVert z_A\rVert - \sqrt{2r_{\max}} = \sqrt{2r_{\max}}\big(\sqrt{1 + r_D/r_{\max}} - 1\big) = \sqrt{2r_{\max}}\,\psi_D/2$, and its Gaussian log-density per unit $\lambda$ is $-(\text{length})^2/(2\lambda) = -\alpha$. In the limit $\lambda/r_{\max} \to 0$ resistant mutants lie in the far tail of the mutation kernel, just inside the ball, so a Laplace-type expansion of $\int_0^1 \pi(y) f_y(y)\,dy$ around that boundary point gives the factor $g(\alpha)$, with the dimension-dependent prefactor accounting for the curvature of the ball and of the Gaussian shells. Inverting $N_0 U g(\alpha_c) = \log 2$ with the asymptotic form of $g$ yields the log-linear growth of $\alpha_c$.

## Depends on

- [Evolutionary rescue rates in Fisher's geometric model](evolutionary-rescue-rates-in-fisher-s-geometric-model.md)

## Sources

- Y. Anciaux, L.-M. Chevin, O. Ronce and G. Martin, "Evolutionary Rescue over a Fitness Landscape", *Genetics* 209 (2018), 265–279, Equations (6), (7a), (7b) and (8), sections "Composite parameter α describing an effective stress level" and "Characteristic stress level", <https://doi.org/10.1534/genetics.118.300908> (PMC5937192).
