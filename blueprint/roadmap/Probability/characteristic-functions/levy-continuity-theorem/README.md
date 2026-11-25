# Lévy's continuity theorem

Let $d \in \mathbb{N}$, let $(\mu_n)_{n \in \mathbb{N}}$ be a sequence of probability measures on the Euclidean space $\mathbb{R}^d$, and let $\varphi : \mathbb{R}^d \to \mathbb{C}$. If the characteristic functions satisfy $\hat\mu_n(t) \to \varphi(t)$ for every $t \in \mathbb{R}^d$, and $\varphi$ is continuous at $0$, then $\varphi$ is the characteristic function of a probability measure $\mu$ on $\mathbb{R}^d$, and $\mu_n$ converges weakly to $\mu$.

## Idea

The theorem turns pointwise convergence of characteristic functions, which is often easy to compute, into weak convergence of the laws; this is the route of the classical proof of the central limit theorem. Continuity of the limit at $0$ is what prevents mass from escaping to infinity: in dimension one, $\mu\{|x| \ge 2/u\} \le \frac{1}{u} \int_{-u}^{u} (1 - \hat\mu(t)) \, dt$ for every $u > 0$ (the integral is real, since $\hat\mu(-t) = \overline{\hat\mu(t)}$), so the behaviour of the characteristic functions near $0$ controls the tails uniformly in $n$, and the sequence is tight. Tightness gives weakly convergent subsequences, every limit has characteristic function $\varphi$, and since a characteristic function determines its law, all limits agree. The condition cannot be dropped: the normal laws with mean $0$ and variance $n$ have characteristic functions $e^{-nt^2/2}$, which converge to a function equal to $1$ at $0$ and $0$ elsewhere, and no limit law exists.

## Statements

- [Lévy's continuity theorem](levy-continuity-of-char-fun.md)

## Background

- [Tight families of probability measures](../../convergence-of-measures/tightness-of-probability-measures/README.md)

## Sources

- P. Billingsley, *Probability and Measure*, 3rd ed., Wiley, 1995.
