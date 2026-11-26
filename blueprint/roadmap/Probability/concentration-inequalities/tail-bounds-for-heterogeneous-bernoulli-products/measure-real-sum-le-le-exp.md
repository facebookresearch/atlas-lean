# Hoeffding lower tail bound

Let $k \in \mathbb{N}$, $p_1, \dots, p_k \in [0, 1]$, and let $S$ be the number of successes among $k$ independent Bernoulli trials with success probabilities $p_1, \dots, p_k$ (the product law on $\{0,1\}^k$). Let $c, T \in \mathbb{R}$ with $c \le p_i$ for every $i$ and $T \le k c$. Then

$$\mathbb{P}(S \le T) \le \exp\!\left( -\frac{2 (k c - T)^2}{k} \right).$$

Division by zero is read as $0$, so for $k = 0$ the right-hand side is $1$ and the bound is trivial.
