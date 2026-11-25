# The least-squares slope is linear in the responses

For real vectors $x$ and $y$ indexed by a finite set, the least-squares slope
$\hat b = S_{xy} / S_{xx}$, with $S_{xy} = \sum_j (x_j - \bar x)(y_j - \bar y)$ and $\bar x$ the
mean of the $x_j$, is

$$\hat b = \sum_j \frac{x_j - \bar x}{S_{xx}}\, y_j,$$

with the convention $x/0 = 0$: both sides are $0$ when $S_{xx} = 0$.
