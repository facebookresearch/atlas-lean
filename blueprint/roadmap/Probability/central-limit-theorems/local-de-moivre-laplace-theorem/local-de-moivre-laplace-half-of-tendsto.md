# Local limit theorem for the simple random walk

Let $k : \mathbb{N} \to \mathbb{Z}$ be a sequence of integers with
$2 k_n / \sqrt{2n} \to x \in \mathbb{R}$. Then

$$\binom{2n}{(n + k_n)^+} 2^{-2n} \sim \frac{1}{\sqrt{\pi n}}\, e^{-x^2/2} \qquad (n \to \infty),$$

where $(n + k_n)^+ = \max(n + k_n, 0)$. For the simple random walk $S$, the left side is
$P(S_{2n} = 2k_n)$ whenever $-n \le k_n \le n$, and the scaling hypothesis forces this for all
large $n$.
