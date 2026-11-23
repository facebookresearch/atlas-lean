# Canonical feature map of a reproducing kernel Hilbert space

Let $H$ be a real reproducing kernel Hilbert space of functions on a set $X$: a Hilbert space of functions $X \to \mathbb{R}$ in which each evaluation $f \mapsto f(x)$ is a continuous linear functional. The canonical feature map sends $x \in X$ to the representer $\varphi(x) \in H$ of evaluation at $x$, the unique element with $\langle f, \varphi(x) \rangle = f(x)$ for every $f \in H$. The reproducing kernel is $k(x, y) = \langle \varphi(x), \varphi(y) \rangle$, so that $\varphi(x) = k(\cdot, x)$.

## Idea

The feature map sends an arbitrary set, with no linear structure, into a Hilbert space (injectively only when the functions of $H$ separate points; for the constant kernel $1$ all points have the same feature), and the kernel computes the inner products of the embedded points without ever writing them out. This is the basis of kernel methods: an algorithm that only uses inner products runs in $H$ by evaluating $k$. The kernel is symmetric and positive definite, and $\|\varphi(x)\|^2 = k(x, x)$. For example, on $X = \mathbb{R}^d$ the space of linear functions $y \mapsto \langle a, y \rangle$ with norm $|a|$ has kernel $k(x, y) = \langle x, y \rangle$; richer spaces give the Gaussian kernel $e^{-|x - y|^2/(2\sigma^2)}$. Conversely, every positive-definite kernel arises from exactly one such space (the Moore–Aronszajn theorem).

## Statements

- [Canonical feature map of a reproducing kernel Hilbert space](feature-map.md)
- [Scalar kernel of a real reproducing kernel Hilbert space](kernel-value.md): definition of the kernel of the space, used by the facts below
- [Symmetry of the kernel](kernel-value-comm.md): basic property of the kernel: symmetry
- [Kernel functions are feature maps](feature-map-apply.md): basic property: the feature map at $x$ is the function $k(\cdot, x)$
- [Reproducing property of the feature map](inner-feature-map.md): reproducing property
- [Norm of a feature map](norm-feature-map.md): basic property: $\|k(\cdot, x)\|^2 = k(x, x)$
- [Operator-valued and scalar kernels](kernel-eq-smul.md): relation between the operator-valued and the scalar kernel
- [The kernel Gram matrix of the representer theorem](kernel-gram-apply.md): the Gram matrix of the kernel
- [The kernel of an RKHS is a positive-definite kernel](is-pos-def-kernel-kernel-value.md): basic property: the kernel is positive definite
- [Continuity of the feature map](continuous-feature-map-of-continuous-ker.md): basic property: continuity for a continuous kernel

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample test*, Journal of Machine Learning Research (2012).
