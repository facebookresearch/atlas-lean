# Dissipative system

The system of differential equations $y' = f(x, y)$, with $f : [x_0, \infty) \times \mathbb{R}^m \to \mathbb{R}^m$, is *dissipative* on $[x_0, \infty)$ if

$$\langle f(x, u) - f(x, v),\ u - v \rangle \le 0 \qquad \text{for all } x \ge x_0 \text{ and all } u, v \in \mathbb{R}^m,$$

where $\langle \cdot, \cdot \rangle$ is the Euclidean inner product.

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 5, Definition 15, inequality (93). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
