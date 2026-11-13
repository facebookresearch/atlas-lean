# Landen form series

For real numbers $a, b, c, d$, viewed as the matrix $g$ with rows
$(a, b)$ and $(c, d)$, this is the power series
$u \cdot G_g(u) = \frac{cu}{a - cu} - \frac{du}{b - du} \in \mathbb{R}[[u]]$, where
$G_g(t) = \frac{c}{a - ct} - \frac{d}{b - dt}$. Here the power series of $\frac{cu}{a - cu}$ is
$\sum_{n \ge 1} (c/a)^n u^n$ if $a \neq 0$, the constant $-1$ if $a = 0$ and $c \neq 0$, and
$0$ if $a = c = 0$; likewise for $\frac{du}{b - du}$ with $b, d$ in place of $a, c$. For
$g \in GL_2(\mathbb{R})$ the last case does not occur.

## Sources

- Ken Kamano, *A Generalization of the Landen Connection Formula and Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2, the function `G_g(t)` before Table 1.
