# Cell Mean

Let $\alpha$ be a finite set, $p : \alpha \to \mathbb{R}$ a weight, $G : \alpha \to C$ an observation map, $Y : \alpha \to \mathbb{R}$ and $c \in C$. With the cell mass $m_p(c) = \sum_{x : G(x) = c} p(x)$, the cell mean is

$$\bar Y_c = \frac{1}{m_p(c)} \sum_{x \in \alpha,\ G(x) = c} p(x)\, Y(x),$$

with the convention $t / 0 = 0$, so the cell mean is $0$ on a cell of mass $0$. For nonnegative weights and a cell of positive mass, $\bar Y_c$ is the conditional expectation $E[Y \mid G = c]$ under the law proportional to $p$. For signed weights it is only a weighted quotient: with both points of a cell weighted $(2, -1)$ and $Y = (0, 1)$, it equals $-1$, which no probability law on those values has as its mean.
