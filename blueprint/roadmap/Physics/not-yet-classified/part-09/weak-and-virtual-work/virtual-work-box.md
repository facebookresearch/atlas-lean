# Virtual work identity on a box

Let $[a, b] \subset \mathbb{R}^3$ be a box with $a_i < b_i$ for each $i$, and $U$ an open set containing it. Let the stress components $\sigma_{ij}$ be $C^1$ on $U$, with $\sigma(x)$ symmetric for every $x$ in the box, let the virtual displacement $v$ be $C^1$ on $U$, and let the body force satisfy $(\operatorname{div} \sigma)(x) + f(x) = 0$ on the box, where $(\operatorname{div}\sigma)_i = \sum_j \partial_j \sigma_{ij}$. With the small strain $\varepsilon_{ij}(v) = \tfrac12 (\partial_j v_i + \partial_i v_j)$,

$$\int_{[a,b]} \sigma : \varepsilon(v)\, dx = \int_{[a,b]} f \cdot v\, dx + \sum_{i} \Bigl( \int_{\{x_i = b_i\}} (\sigma e_i) \cdot v + \int_{\{x_i = a_i\}} (\sigma (-e_i)) \cdot v \Bigr),$$

the face integrals running over the faces of the box.
