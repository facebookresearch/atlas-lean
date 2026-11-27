# The online normalizer computes the softmax normalizer

Let $V \ge 1$ and $x_1, \dots, x_V \in \mathbb{R}$. Define $m_1 = x_1$, $d_1 = 1$ and, for $2 \le j \le V$,

$$m_j = \max(m_{j-1}, x_j), \qquad d_j = d_{j-1}\, e^{m_{j-1} - m_j} + e^{x_j - m_j}.$$

Then $m_V = \max_k x_k$ and $d_V = \sum_{j=1}^V e^{x_j - m_V}$. Consequently $e^{x_i - m_V} / d_V = \operatorname{softmax}(x)_i$ for every $i$: one pass over the input computes both the maximum and the normalizer of the max-shifted softmax.

The source starts from $m_0 = -\infty$, $d_0 = 0$; its first step gives the values $m_1, d_1$ above, so the statement is the same with real initial values. The statement is about exact real arithmetic; it says nothing about rounding.

## Depends on

- [Softmax](../../not-yet-classified/basic/part-06/softmax.md)

## Proof depends on

- [Softmax](../../not-yet-classified/basic/part-06/softmax.md)

The recurrence is verified by induction on the input length, using the exponential addition law.

## Sources

- M. Milakov and N. Gimelshein, "Online normalizer calculation for softmax", arXiv:1805.02867, 2018, Algorithm 3 and Theorem 1.
