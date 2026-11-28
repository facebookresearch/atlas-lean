# Hoeffding upper tail bound

Let $k \in \mathbb{N}$, $p_1, \dots, p_k \in [0, 1]$, and let $S$ be the number of successes among $k$ independent Bernoulli trials with success probabilities $p_1, \dots, p_k$ (the product law on $\{0,1\}^k$). Let $s, T \in \mathbb{R}$ with $p_i \le s$ for every $i$ and $k s \le T$. Then

$$\mathbb{P}(S \ge T) \le \exp\!\left( -\frac{2 (T - k s)^2}{k} \right).$$

Division by zero is read as $0$, so for $k = 0$ the right-hand side is $1$ and the bound is trivial.
