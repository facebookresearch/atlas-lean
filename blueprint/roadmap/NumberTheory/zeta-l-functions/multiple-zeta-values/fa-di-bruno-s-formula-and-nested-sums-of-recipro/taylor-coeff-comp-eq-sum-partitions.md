# Faà di Bruno's formula for Taylor coefficients

Let $f, g : \mathbb{R} \to \mathbb{R}$,
let $a \in \mathbb{R}$ and let $n$ be a natural number. Suppose that $g$ is $n$ times continuously
differentiable on a neighbourhood of $a$ and that $f$ is $n$ times continuously differentiable on a
neighbourhood of $g(a)$. For a partition $\pi$ of $n$, let $m_i(\pi)$ be the number of parts of
$\pi$ equal to $i$, and let $\ell(\pi) = m_1(\pi) + \cdots + m_n(\pi)$ be its number of parts. Then

$$\frac{(f \circ g)^{(n)}(a)}{n!} = \sum_{\pi} \frac{\ell(\pi)!}{\prod_{i=1}^{n} m_i(\pi)!} \cdot
\frac{f^{(\ell(\pi))}(g(a))}{\ell(\pi)!} \cdot
\prod_{i=1}^{n} \Bigl(\frac{g^{(i)}(a)}{i!}\Bigr)^{m_i(\pi)},$$

where the sum runs over all partitions $\pi$ of $n$.

## Sources

- Serge Iovleff, *About Some Nested Sums of Reciprocal Squared Numbers*, INTEGERS 26 (2026), Article A114, Corollary 1 (quoted as Corollary 4 from the paper's reference [8]).
