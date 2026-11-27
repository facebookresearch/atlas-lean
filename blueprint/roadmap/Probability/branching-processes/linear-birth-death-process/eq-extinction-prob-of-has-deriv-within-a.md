# Uniqueness of the extinction probability solving the backward equation

Let $b, d \ge 0$ and let $\alpha$ be [Kendall's extinction probability](extinction-prob.md) for
birth rate $b$ and death rate $d$. Let $q : \mathbb{R} \to \mathbb{R}$ be continuous on
$[0, \infty)$, with $q(t) \in [0, 1]$ for every $t \ge 0$ and $q(0) = 0$, and suppose that at
every $t \ge 0$ the function $q$ has right derivative

$$q'(t) = d - (b + d)\, q(t) + b\, q(t)^2 .$$

Then $q(t) = \alpha(t)$ for every $t \ge 0$: the extinction probability is the only
$[0, 1]$-valued solution of the backward equation with $q(0) = 0$.
