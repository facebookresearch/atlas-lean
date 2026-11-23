# Convolution of an integrable and a bounded function is uniformly continuous

If $f : \mathbb{R}^d \to \mathbb{R}$ is Lebesgue integrable and $g : \mathbb{R}^d \to \mathbb{R}$ is
Borel measurable and bounded, then the convolution
$(f * g)(x) = \int_{\mathbb{R}^d} f(x - y)\, g(y)\, dy$ is uniformly continuous on $\mathbb{R}^d$.

## Idea

Convolution averages one function against translates of another, and inherits regularity from
the better of the two. Here
$|f * g(x + h) - f * g(x)| \le \sup |g| \cdot \int |f(z + h) - f(z)|\, dz$, and translation is
continuous in $L^1$: the right side tends to $0$ as $h \to 0$, uniformly in $x$.

## Statements

- [Convolution of an integrable and a bounded function is uniformly continuous](uniform-continuous-convolution-integrabl.md)
