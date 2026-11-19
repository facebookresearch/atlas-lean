# Joint prior covariance in Gaussian-process regression

For a kernel $k : X \times X \to \mathbb{R}$, a real number $\sigma^2$ and finite families of test inputs $x^* = (x^*_i)_{i \in \tau}$ and training inputs $x = (x_j)_{j \in \nu}$, the joint prior covariance matrix is the $(\tau \sqcup \nu) \times (\tau \sqcup \nu)$ block matrix

$$\begin{pmatrix} K(x^*, x^*) & K(x^*, x) \\ K(x, x^*) & K(x, x) + \sigma^2 I \end{pmatrix},$$

where $K(a, b) = (k(a_i, b_j))_{i, j}$ is the [kernel matrix](kernel-matrix.md). When $k$ is positive semidefinite
and $\sigma^2 \ge 0$, it is the covariance of the test values $f(x^*)$ and the noisy training targets
$y = f(x) + \varepsilon$, $\varepsilon \sim N(0, \sigma^2 I)$ independent of $f \sim \mathrm{GP}(0, k)$.
