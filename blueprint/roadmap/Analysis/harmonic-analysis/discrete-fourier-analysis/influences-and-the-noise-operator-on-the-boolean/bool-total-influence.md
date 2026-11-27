# Total influence on the Boolean cube

For a function $f$ from the Boolean cube
$\{-1, 1\}^n$ to $\mathbb{R}$, the total influence of $f$ is the sum of the influences of its $n$
coordinates, $\mathrm{I}[f] = \sum_{i=0}^{n-1} \mathrm{Inf}_i[f]$, where
$\mathrm{Inf}_i[f] = \mathbb{E}_x \left[\left(\frac{f(x) - f(x^{\oplus i})}{2}\right)^2\right]$,
$x^{\oplus i}$ is $x$ with its $i$-th coordinate flipped and $\mathbb{E}_x$ is the uniform average
over the points $x$ of the cube.
