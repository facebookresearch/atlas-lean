# A limit of SGD from zero that interpolates is the minimum-norm interpolant

Let the [stochastic gradient iterates](sgd-iterate.md) of a linear model, started at $w_0 = 0$, converge to $w$, and let $w$ interpolate the labels. Then $\lVert w\rVert \le \lVert w'\rVert$ for every interpolant $w'$.

Proof: the iterates lie in [the span of the data](sgd-iterate-mem-span.md), which is finite-dimensional and hence closed, so $w$ lies in it too; apply [minimality of the interpolant in the span](norm-le-of-mem-span-of-interpolates.md).

The convergence of SGD is a hypothesis: the source observes that SGD "will often converge" to this solution. The minimum-norm solution is the kernel solution of the source, and the source also notes that minimum norm alone does not predict generalization.

## Sources

- C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Section 5 ("out of all models that exactly fit the data, SGD will often converge to the solution with minimum norm").
