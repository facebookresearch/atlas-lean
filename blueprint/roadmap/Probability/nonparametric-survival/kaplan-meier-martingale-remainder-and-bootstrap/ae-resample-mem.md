# Bootstrap resamples stay in any measurable set containing the data

Let $\alpha$ be a measurable space with a distinguished element $0$, and $x_0, x_1, \dots \in \alpha$ the data. For $n \ge 1$ let $P_n = \frac1n \sum_{i < n} \delta_{x_i}$ be the empirical law of the first $n$ data points, and let $P_0 = \delta_0$. The bootstrap world of $x$ is the product probability measure

$$W_x = \bigotimes_{n \in \mathbb N} \bigotimes_{m \in \mathbb N} P_n$$

on arrays $\omega = (\omega_{n,m})_{n, m \in \mathbb N}$, so that row $n$ consists of independent draws from $P_n$; the resample of size $n$ is $(\omega_{n,0}, \dots, \omega_{n,n-1})$.

Let $S \subseteq \alpha$ be measurable and $n \in \mathbb N$, and suppose $x_i \in S$ for every $i < n$. Then for $W_x$-almost every $\omega$, $\omega_{n,i} \in S$ for every $i < n$.
