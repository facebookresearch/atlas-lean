# Kernel density estimator

For a kernel $K : \mathbb{R} \to \mathbb{R}$, a bandwidth $h \in \mathbb{R}$ and a sample $x = (x_1, \dots, x_n)$ of real numbers, the kernel density estimator at $t \in \mathbb{R}$ is

$$\hat f_h(t) = \frac{1}{nh} \sum_{i=1}^{n} K\Big(\frac{t - x_i}{h}\Big),$$

with the conventions $0^{-1} = 0$ and $y/0 = 0$, so the estimator is $0$ when $n = 0$ or $h = 0$.
