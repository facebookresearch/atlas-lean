# Evolutionary rescue rates in Fisher's geometric model

**Model.** An asexual population of initial size $N_0 \gg 1$ experiences an abrupt environmental shift at $t = 0$. A genotype with breeding values $z \in \mathbb{R}^n$ has Malthusian growth rate

$$r(z) = r_{\max} - \tfrac12\,\lVert z - o\rVert^2$$

with environment-dependent optimum $o$. Put the new optimum at $o = 0$; the ancestral (previously optimal) phenotype $z_A$ then has growth rate $r(z_A) = -r_D < 0$, so $\lVert z_A\rVert = \sqrt{2(r_D + r_{\max})}$. Mutations arise as a Poisson process at rate $U$ per capita per unit time and add $dz \sim \mathcal{N}(0, \lambda I_n)$ to the phenotype. Each lineage follows an independent Feller diffusion with growth rate $r$ and reproductive variance $\sigma$, so a single resistant mutant ($r > 0$) establishes with probability $\pi = 1 - e^{-2r/\sigma}$. Assume strong selection and weak mutation, $U < U_C = n^2\lambda/4$, so rescue comes from single-step mutants of the dominant genotype $z_A$ (de novo, or standing at house-of-cards mutation–selection balance before the shift).

**Mutant growth rates.** The scaled growth rate $y = r/r_{\max} \in (-\infty, 1]$ of a random mutant of $z_A$ has density, with $y_D = r_D/r_{\max}$,

$$f_y(y) = \frac{\exp\!\big(-\tfrac{r_{\max}}{\lambda}(2 + y_D - y)\big)\,\big(\tfrac{r_{\max}}{\lambda}\big)^{n/2}(1-y)^{n/2-1}\,{}_0F_1\!\big(\tfrac n2;\,(\tfrac{r_{\max}}{\lambda})^2(1+y_D)(1-y)\big)}{\Gamma(n/2)} .$$

**Rescue probability.** The probability of evolutionary rescue is

$$P_R = 1 - e^{-N_0\,\omega}, \qquad \omega = \omega_{DN} \ (\text{clonal start}), \quad \omega = \omega_{DN} + \omega_{SV} \ (\text{start at mutation–selection balance}),$$

with per-capita rescue rates from de novo and standing variation

$$\omega_{DN} = \frac{U}{r_D}\int_0^1 \pi(y)\,f_y(y)\,dy, \qquad \omega_{SV} = U\int_0^1 \frac{\pi(y)}{c_H(y)}\,f_y(y)\,dy, \qquad \pi(y) = 1 - e^{-2 y r_{\max}/\sigma},$$

where $c_H(y) = 1/\mathbb{E}(1/c \mid y)$ is the harmonic mean, over mutants of scaled growth $y$ in the new environment, of their cost $c = \lVert z - z_A\rVert^2/2$ in the previous environment. For $n \ge 2$, $c_H(y) = \lambda \big/ \big(e^{v(y)} E_{(n-1)/2}(v(y))\big)$ with $v(y) = \frac{r_{\max}}{\lambda}\big(2 + y_D - 2\sqrt{(1+y_D)(1-y)} - y\big)$ and $E_k(z) = \int_1^\infty e^{-zt}t^{-k}\,dt$.

Unlike context-independent rescue models, where the proportion $q_R$ of rescue mutations and their cost are fixed, here both depend on the stress through $r_D$, because a larger shift of the optimum leaves fewer and weaker mutants with positive growth.

## Proof sketch

The number of declining wild-type individuals is $N_0 e^{-r_D t}$, so the expected total number of de novo mutants is $N_0 U/r_D$; each is resistant and establishes with probability $\int_0^1 \pi f_y$, and the number of successful rescuers is Poisson, giving $P_R = 1 - e^{-N_0\omega_{DN}}$. Under the house-of-cards approximation, the standing number of mutants in class $[y, y+dy]$ is Poisson with mean $N_0 U f_y(y)\,dy / c_H(y)$ (mutation input divided by the rate of purging), and each establishes with probability $\pi(y)$, giving $\omega_{SV}$. The density $f_y$ follows from the noncentral chi-square law of $\lVert z_A + dz\rVert^2/\lambda$ with $n$ degrees of freedom and noncentrality $\lVert z_A\rVert^2/\lambda$, transformed through $y = 1 - \lVert z\rVert^2/(2 r_{\max})$.

## Sources

- Y. Anciaux, L.-M. Chevin, O. Ronce and G. Martin, "Evolutionary Rescue over a Fitness Landscape", *Genetics* 209 (2018), 265–279, section "Model", Equations (1)–(5), <https://doi.org/10.1534/genetics.118.300908> (PMC5937192).
