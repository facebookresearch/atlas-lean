# Soft-margin support vector machine objective with offset

**Soft-margin support vector machine objective with offset** (Schölkopf, Herbrich and
Smola, *A generalized representer theorem*, COLT 2001, Example 2, equation (28) with
$g(\|f\|) = \|f\|^2$). Let $H$ be a real reproducing kernel Hilbert space of functions on a set
$X$. For inputs $x_1, \dots, x_m \in X$, labels $y_i \in \mathbb{R}$, a parameter
$\lambda \in \mathbb{R}$, a function $f \in H$ and an offset $b \in \mathbb{R}$, it is
$\lambda^{-1} \sum_i \max(0, 1 - y_i (f(x_i) + b)) + \|f\|^2$, where $0^{-1} = 0$.
