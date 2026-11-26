# Steady-state cell density and mean phenotype under concave quadratic fitness

Consider the [phenotype-structured tumour model](phenotype-structured-model-of-hypoxia-and-acidity-selection.md) with fitness of the strictly concave form

$$R(S_o,S_g,S_l,\rho,y_1,y_2)=\frac{\gamma_oS_o}{\alpha_o+S_o}\big(1-\varphi_o(S_o)\big)+\frac{\gamma_gS_g}{\alpha_g+S_g}\varphi_o(S_o)-\eta_o\big(y_2-\varphi_o(S_o)\big)^2-\eta_l\big(y_1-\varphi_l(S_l)\big)^2-\kappa\rho,$$

where $\varphi_o,\varphi_l:\mathbb R_+\to[0,1]$. Suppose spontaneous phenotypic changes and random motility act on slower time scales than proliferation and death. Then, by a formal time-scale separation and asymptotic argument, the steady-state local phenotypic distribution $n_\infty(x,\cdot)$ is unimodal and, at each $x\in[0,L]$ where the steady-state density $\rho_\infty(x)$ is positive (so that the mean traits $\mu_{1,\infty},\mu_{2,\infty}$ are defined), the density and mean traits satisfy

$$R=0,\qquad \partial_{y_1}R=0,\qquad \partial_{y_2}R=0\quad\text{at }(y_1,y_2)=(\mu_{1,\infty},\mu_{2,\infty}),$$

which gives explicitly

$$\rho_\infty(x)=\frac1\kappa\left[\frac{\gamma_oS_{o,\infty}}{\alpha_o+S_{o,\infty}}\big(1-\varphi_o(S_{o,\infty})\big)+\frac{\gamma_gS_{g,\infty}}{\alpha_g+S_{g,\infty}}\varphi_o(S_{o,\infty})\right],$$

$$\mu_{1,\infty}(x)=\varphi_l\big(S_{l,\infty}(x)\big),\qquad \mu_{2,\infty}(x)=\varphi_o\big(S_{o,\infty}(x)\big),$$

where $S_{o,\infty},S_{g,\infty},S_{l,\infty}$ are the steady-state abiotic concentrations.

## Depends on

- [Phenotype-structured model of oxygen- and lactate-driven selection](phenotype-structured-model-of-hypoxia-and-acidity-selection.md)

## Expansion

In the slow-mutation regime the distribution concentrates near the maximiser of the fitness in $y$; stationarity requires that the population neither grows nor shrinks there, so the fitness vanishes at the mean trait while its gradient in $y$ vanishes because the mean sits at the maximiser. With quadratic penalties the maximiser is $(\varphi_l,\varphi_o)$, and substituting it into $R=0$ gives $\rho_\infty$. The result is formal, not a theorem; the authors confirm it numerically. It explains why the mean phenotype tracks the fittest phenotype pointwise and why density is set by the local proliferation rate divided by $\kappa$.

## Sources

- G. Fiandaca, M. E. Delitala, T. Lorenzi, "A Mathematical Study of the Influence of Hypoxia and Acidity on the Evolutionary Dynamics of Cancer", Bull. Math. Biol. 83 (2021), appendix on steady-state properties, Equations (22)–(25), <https://doi.org/10.1007/s11538-021-00914-3>, PMCID PMC8205926.
