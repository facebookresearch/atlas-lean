# Kolmogorov three-series theorem, necessity, first series

Let $(X_n)_{n \ge 0}$ be a
sequence of independent measurable real random variables on a probability space
$(\Omega, \mu)$ whose partial sums converge almost surely: there is a function
$S : \Omega \to \mathbb{R}$ such that $\sum_{i < n} X_i(\omega) \to S(\omega)$ as $n \to \infty$
for $\mu$-almost every $\omega$. Then for every $A > 0$ the tail probabilities are summable:
$\sum_n \mu(\{\omega : |X_n(\omega)| > A\}) < \infty$.

Proof: argue by contradiction via the second Borel–Cantelli lemma. If the tail probabilities
summed to $\infty$, the events $\{|X_n| > A\}$ would occur infinitely often with probability
one; but almost-sure convergence of the partial sums forces $X_n \to 0$ almost surely, hence
eventually $|X_n| \le A$.
