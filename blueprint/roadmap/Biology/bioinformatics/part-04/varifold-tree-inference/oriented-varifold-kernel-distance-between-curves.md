# Oriented varifold kernel distance between curves

Let $X\subset\mathbb R^n$ be a smooth, regular, oriented curve of finite length with unit oriented tangent $\vec t(x)\in\mathbb S^{n-1}$, and let $W$ be a reproducing kernel Hilbert space of test functions on $\mathbb R^n\times\mathbb S^{n-1}$ with positive definite kernel $k$. The **oriented varifold** of $X$ is the linear functional

$$\mu_X:W\to\mathbb R,\qquad \omega\mapsto\int_X\omega\bigl(x,\vec t(x)\bigr)\,d\ell(x),$$

where $\ell$ is arc length. For the separable Gaussian kernel $k\bigl((x_1,t_1),(x_2,t_2)\bigr)=e^{-\|x_1-x_2\|^2/\sigma_x^2}e^{-\|t_1-t_2\|^2/\sigma_t^2}$, the induced inner product on $W^*$ is

$$\langle\mu_X,\mu_Y\rangle_{W^*}=\iint_{X\times Y}e^{-\|x-y\|^2/\sigma_x^2}\,e^{-\|\vec t(x)-\vec t(y)\|^2/\sigma_t^2}\,d\ell(x)\,d\ell(y),$$

and $d_{W^*}(X,Y)=\|\mu_X-\mu_Y\|_{W^*}$ is a distance on such curves (the map $X\mapsto\mu_X$ is injective for this kernel).

Properties:

- **Parameterization invariance:** $\mu_X$ depends on the image and orientation of $X$, not on a parameterization, and has closed-form approximations for polygonal curves.
- **Additivity:** for curves meeting at most in a null set, $\mu_{X\cup Y}=\mu_X+\mu_Y$; hence two curves sharing a common sub-arc are at the distance determined only by their non-shared parts.
- **Robustness:** $d_{W^*}(X,\phi\cdot Y)^2\to d_{W^*}(X,Y)^2$ as $\|\phi-\mathrm{id}\|_\infty\to0$ and $\|d\phi-I\|_F\to0$ for diffeomorphic deformations $\phi$; in practice $\sigma_x$ and $\sigma_t$ are chosen well above the deformation sizes.

## Expansion

The reproducing property represents point evaluations $\delta_{(x,t)}$ by kernel sections, so $\langle\delta_{(x_1,t_1)},\delta_{(x_2,t_2)}\rangle_{W^*}=k((x_1,t_1),(x_2,t_2))$; integrating along both curves gives the double-integral formula. The spatial factor compares positions and the tangent factor compares local directions, which is what allows the distance to tell apart branches that leave a common point in different directions. In single-cell trajectory inference, the curves are integral curves of an RNA velocity field in gene-expression space, traced from a root state to each cell.

## Sources

- E. Maignant, T. Conrad and C. von Tycowicz, "Tree inference with varifold distances", in *Geometric Science of Information* (GSI 2025), Lecture Notes in Computer Science, Springer (2025), 290–299, Section 3 (Distances between curves as oriented varifolds), <https://doi.org/10.1007/978-3-032-03921-7_30>; preprint arXiv:2507.11313, <https://doi.org/10.48550/arXiv.2507.11313>.
