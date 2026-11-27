# Binomial transition kernel for loss-of-function counts

For real numbers $s$ and $U$, natural numbers $N$ and $N'$, and counts $i \in \{0, \dots, N\}$ and $j \in \{0, \dots, N'\}$, the transition weight from $i$ loss-of-function copies among $N$ to $j$ copies among $N'$ is

$$\binom{N'}{j} \pi_i^{\,j} (1 - \pi_i)^{N' - j}, \qquad \pi_i = (1 - s)\frac{i}{N} + U,$$

with the convention $i/0 = 0$. When $0 \le \pi_i \le 1$ it is the probability of $j$ successes in binomial sampling of $N'$ copies with success probability $\pi_i$.
