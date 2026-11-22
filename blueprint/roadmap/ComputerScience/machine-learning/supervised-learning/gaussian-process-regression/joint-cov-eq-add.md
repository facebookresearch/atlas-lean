# The joint covariance as a kernel matrix plus noise

For a kernel
$k : X \times X \to \mathbb{R}$, a real number $\sigma^2$, test inputs $x^* = (x^*_i)_{i \in \tau}$
and training inputs $x = (x_j)_{j \in \nu}$, the joint covariance of $k$, $\sigma^2$, $x^*$ and $x$
equals $K + D$, where $K$ is the kernel matrix of the combined family $(x^*, x)$ indexed by
$\tau \sqcup \nu$ and $D$ is the diagonal matrix with entry $0$ at each test index and $\sigma^2$
at each training index.
