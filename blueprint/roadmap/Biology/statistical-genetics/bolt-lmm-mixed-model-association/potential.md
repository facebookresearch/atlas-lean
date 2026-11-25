# Coordinate-ascent potential for one SNP effect

Let $X$ be a real $n \times m$ matrix with columns $x_j$, let $y \in \mathbb{R}^n$, let $\sigma_e^2$ be real, let $q_1, \dots, q_m$ be measures on $\mathbb{R}$, and let $j \in \{1, \dots, m\}$. The coordinate-ascent potential of SNP $j$ is the function

$$f_j(b) = \frac{b\, x_j^\top r_j - \|x_j\|^2 b^2 / 2}{\sigma_e^2}, \qquad b \in \mathbb{R},$$

where $r_j$ is the [partial residual](partial-residual.md) and $\|x_j\|^2$ the [squared column norm](col-norm-sq.md), with the convention $x/0 = 0$ when $\sigma_e^2 = 0$. When $\sigma_e^2 > 0$ and the other factors are probability measures with finite second moments, it is the part of the expected log-likelihood, under the other factors, that depends on the $j$-th effect $b$ ([the ELBO as a function of one factor](exists-elbo-update-eq.md)).
