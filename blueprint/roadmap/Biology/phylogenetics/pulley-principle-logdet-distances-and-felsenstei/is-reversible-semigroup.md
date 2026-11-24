# Reversible semigroup of transition matrices

Let $S$ be a finite state set, $\pi : S \to \mathbb{R}$ and $P_t : S \times S \to \mathbb{R}$ a family indexed by real $t$. The family is a reversible semigroup for $\pi$ if

- $\sum_{b} P_s(a, b) P_t(b, c) = P_{s+t}(a, c)$ for all real $s, t$ and states $a, c$ (Chapman–Kolmogorov), and
- $\pi(a) P_t(a, b) = \pi(b) P_t(b, a)$ for all $t, a, b$ (detailed balance).
