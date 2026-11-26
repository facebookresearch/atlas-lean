# Convolution of sequences on the integers

The convolution of two complex sequences $f, g : \mathbb{Z} \to \mathbb{C}$ is the sequence

$$
(f * g)(n) = \sum_{m \in \mathbb{Z}} f(m)\, g(n - m), \qquad n \in \mathbb{Z},
$$

where the sum is taken to be $0$ when the family $(f(m)\, g(n - m))_{m \in \mathbb{Z}}$ is not summable. For $f \in \ell^1(\mathbb{Z}, \mathbb{C})$ and $g \in \ell^p(\mathbb{Z}, \mathbb{C})$ with $1 \le p \le \infty$ the series always [converges](summable-int-conv-term.md).
