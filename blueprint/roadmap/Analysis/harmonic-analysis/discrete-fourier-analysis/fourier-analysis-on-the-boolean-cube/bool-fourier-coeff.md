# Fourier coefficient on the Boolean cube

For $n \in \mathbb{N}$, a function
$f : \{-1, 1\}^n \to \mathbb{R}$ and a set $S \subseteq \{0, \dots, n-1\}$, the normalized Fourier
coefficient of $f$ at $S$ is
$\hat f(S) = \frac{1}{|\{-1, 1\}^n|} \sum_{x \in \{-1, 1\}^n} f(x) \chi_S(x)$, where
$\chi_S(x) = \prod_{i \in S} x_i$. That is, $\hat f(S)$ is the uniform expectation of $f \chi_S$.
