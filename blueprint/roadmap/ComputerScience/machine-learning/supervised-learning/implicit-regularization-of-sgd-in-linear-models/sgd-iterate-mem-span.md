# SGD from zero stays in the span of the data

Every [stochastic gradient iterate](sgd-iterate.md) $w_t$ of a linear model started at $w_0 = 0$ lies in the span of the data points: $w_t = \sum_i \alpha_i x_i = X^\top \alpha$ for some coefficients $\alpha$.

Proof: by induction, each update subtracts a multiple of a data point.

## Sources

- C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Section 5.
