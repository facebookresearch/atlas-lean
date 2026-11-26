# Arikan-Telatar: rate of polarization

For every BMS channel $W$ with $I(W) > 0$ and every $\beta < 1/2$,

$$
\lim_{N \to \infty} \frac{\#\{i \le N : Z(W_N^{(i)}) \le 2^{-N^{\beta}}\}}{N} = I(W),
$$

while for every $\beta > 1/2$ the corresponding fraction tends to $0$. For $\ell \times \ell$ polarizing kernels the threshold $1/2$ is replaced by the kernel exponent $E(K) \le 1$, which tends to $1$ as $\ell \to \infty$.

## Proof sketch

Once $Z_j$ is small, squaring at a constant fraction of the steps (the $+$ steps, about half of them by the law of large numbers) and at most doubling at the others makes $\log_2(1/Z_n)$ grow like $2^{n/2 - o(n)} = N^{1/2 - o(1)}$. A bootstrapping argument first brings $Z_j$ below a small constant on a set of probability close to $I(W)$ using almost sure convergence, then applies the squaring dynamics. The converse uses $Z(W^{-}) \ge Z(W)$.

## Depends on

- [The polarization martingale](polarization-martingale.md)

## Proof depends on

- [The polarization martingale](polarization-martingale.md)

## Sources

- Erdal Arikan, Emre Telatar, "On the rate of channel polarization", ISIT (2009); arXiv:0807.3806.
- Satish Babu Korada, Eren Sasoglu, Rudiger Urbanke, "Polar codes: characterization of exponent, bounds, and constructions", IEEE Transactions on Information Theory 56(12) (2010).
