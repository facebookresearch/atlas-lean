# Message polynomial of an MSB-first bit sequence

Let $B = (b_0, b_1, \dots, b_{\ell - 1}) \in \{0, 1\}^{\ell}$ be a finite bit sequence of declared length $\ell$, ordered most significant bit first (with any leading zeros counted in $\ell$). Its message polynomial over $\mathbb{F}_2$ is

$$m(B) = \sum_{j=0}^{\ell - 1} \beta(b_j) X^{\ell - 1 - j} \in \mathbb{F}_2[X],$$

where $\beta(0) = 0$ and $\beta(1) = 1$. When $\ell = 0$, the sum is empty and $m(B) = 0$.
