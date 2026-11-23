# Erdős Problem 1196 on primitive sets

There is a function $o : \mathbb{N} \to \mathbb{R}$
with $o(x) \to 0$ as $x \to \infty$ such that for every natural number $x > 0$ and every
primitive set $A$ of natural numbers contained in $[x, \infty)$, the series
$\sum_{a \in A} \frac{1}{a \log a}$ is summable and $\sum_{a \in A} \frac{1}{a \log a} < 1 + o(x)$.
Here a set of natural numbers is primitive if no element divides a different element, and the
term for $a = 1$, where $\log a = 0$, is taken to be $0$.

This answers affirmatively a question of Erdős, Sárközy and Szemerédi. It was solved by
GPT-5.4 Pro (prompted by Price), which proved the stronger bound
$\sum_{a \in A,\ a > x} \frac{1}{a \log a} \le 1 + O(1/\log x)$ for every primitive set $A$.

## Sources

- T. F. Bloom, Erdős Problem #1196, https://www.erdosproblems.com/1196.
- Boris Alexeev, Kevin Barreto, Yanyang Li, Jared Duker Lichtman, Liam Price, Jibran Iqbal Shah, Quanyu Tang, and Terence Tao, *Primitive sets and von Mangoldt chains: Erdős Problem #1196 and beyond*, arXiv:2605.00301 (2026), https://arxiv.org/abs/2605.00301.
