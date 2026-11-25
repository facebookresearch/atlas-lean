# Length of a polyline

The length of a finite list of points of the Euclidean plane $\mathbb{R}^2$ is defined recursively: the empty list and a one-point list have length $0$, and

$$\mathrm{len}(a, b, p_3, \dots, p_n) = \|a - b\| + \mathrm{len}(b, p_3, \dots, p_n) .$$

So $\mathrm{len}(p_1, \dots, p_n) = \sum_{i=1}^{n-1} \|p_i - p_{i+1}\|$.
