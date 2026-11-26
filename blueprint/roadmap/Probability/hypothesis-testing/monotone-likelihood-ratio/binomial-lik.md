# Binomial likelihood

Let $N \in \mathbb{N}$ and $p : \mathbb{R} \to \mathbb{R}$ a parameter-dependent success probability. The binomial likelihood is

$$L(n, \theta) = \binom{N}{n} p(\theta)^n (1 - p(\theta))^{N - n}, \qquad n \in \mathbb{N},\ \theta \in \mathbb{R},$$

which is $0$ for $n > N$ since $\binom{N}{n} = 0$.
