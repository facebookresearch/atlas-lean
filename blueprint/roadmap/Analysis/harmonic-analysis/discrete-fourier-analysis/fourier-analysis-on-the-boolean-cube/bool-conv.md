# Convolution on the Boolean cube

For $f, g : \{-1, 1\}^n \to \mathbb{R}$, the convolution $f * g$ is the function

$$(f * g)(x) = \mathbb{E}_{y}\big[f(y)\, g(x y)\big],$$

with $y$ uniform on the cube and $x y$ the coordinatewise product. On $\mathbb{F}_2^n$ this is
$\mathbb{E}_y[f(y) g(x - y)]$, since $x - y = x + y$ there.

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), Definition 1.24.
