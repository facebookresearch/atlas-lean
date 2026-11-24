# A single neuron lies in the Barron space

For parameters $(a, b, c) \in \mathbb{R} \times \mathbb{R}^d \times \mathbb{R}$, the function
$x \mapsto a \max(\langle b, x \rangle + c, 0)$ is represented by the Dirac mass at $(a, b, c)$, so
its [Barron norm](barron-norm.md) is at most $\lvert a \rvert (\lVert b \rVert_1 + \lvert c \rvert)$,
the path norm of the one-neuron network (compare E, Ma and Wu, *A priori estimates of the
population risk for two-layer neural networks*, §3.1: the Barron norm of a finite two-layer
network is bounded by its path norm).
