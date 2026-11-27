# Centred log-ratio transform of a positive composition

Let $\iota$ be a finite set of $D = |\iota|$ parts and $x = (x_i)_{i \in \iota}$ a
[positive composition](pos-composition.md), so $x_i > 0$ for every part $i$. The centred
log-ratio (CLR) transform of $x$ is the vector $\operatorname{clr}(x) \in \mathbb{R}^\iota$ with

$$\operatorname{clr}(x)_i = \log x_i - \frac{1}{D} \sum_{j \in \iota} \log x_j .$$

Equivalently, $\operatorname{clr}(x)_i = \log\bigl(x_i / g(x)\bigr)$, where
$g(x) = \bigl(\prod_{j \in \iota} x_j\bigr)^{1/D}$ is the geometric mean of the parts. The
transform is defined on strictly positive compositions only, so every logarithm here is of a
positive number; counts with zeros are first made positive, for example by the
[pseudocount rule](with-pseudocount.md).
