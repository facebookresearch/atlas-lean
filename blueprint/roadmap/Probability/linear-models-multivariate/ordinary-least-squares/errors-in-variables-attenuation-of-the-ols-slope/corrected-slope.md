# Measurement-error corrected slope

For data $x, y \in \mathbb{R}^n$ indexed by a finite set of size $n$ and a known or estimated measurement-error variance $\sigma_u^2 \in \mathbb{R}$, the corrected slope of $y$ on $x$ is

$$\hat\beta_c = \frac{S_{xy}}{S_{xx} - n\,\sigma_u^2}, \qquad S_{xy} = \sum_i (x_i - \bar x)(y_i - \bar y),\quad S_{xx} = \sum_i (x_i - \bar x)^2,$$

with the convention that a quotient by $0$ is $0$.
