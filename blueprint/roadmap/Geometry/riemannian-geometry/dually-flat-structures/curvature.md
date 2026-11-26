# Curvature of a connection in coordinates

Let $\Gamma^l_{ij}(x)$ be functions on $\mathbb{R}^n$, read as the coefficients of a connection with $\nabla_{\partial_i} \partial_j = \sum_l \Gamma^l_{ij} \partial_l$. Its curvature at $x$ is

$$R^l_{\ kij}(x) = \partial_i \Gamma^l_{jk}(x) - \partial_j \Gamma^l_{ik}(x) + \sum_{m=1}^{n} \bigl( \Gamma^m_{jk}(x)\, \Gamma^l_{im}(x) - \Gamma^m_{ik}(x)\, \Gamma^l_{jm}(x) \bigr),$$

so that $R(\partial_i, \partial_j)\, \partial_k = \sum_l R^l_{\ kij}\, \partial_l$. Here $\partial_i$ is the partial derivative, taken to be $0$ where the function is not differentiable.
