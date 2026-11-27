# Arikan-Telatar: rate of polarization

For every BMS channel $W$ with $I(W) > 0$, Arikan's $2 \times 2$ kernel, $N = 2^n$ and every $\beta < 1/2$,

$$
\lim_{N \to \infty} \frac{\#\{i \le N : Z(W_N^{(i)}) \le 2^{-N^{\beta}}\}}{N} = I(W).
$$

Conversely, if $I(W) < 1$, then for every $\beta > 1/2$ the fraction of indices with $Z(W_N^{(i)}) < 2^{-N^{\beta}}$ tends to $0$. The hypothesis $I(W) < 1$ is needed: for a perfect channel every synthesized channel has $Z = 0$. For an $\ell \times \ell$ polarizing kernel $G$ the threshold $1/2$ is replaced by the exponent $E(G) \le 1$, computed from the partial distances of $G$, with $N = \ell^n$. It is the best achievable exponent $E_\ell = \max_G E(G)$ over $\ell \times \ell$ kernels that tends to $1$ as $\ell \to \infty$, not the exponent of every kernel.

## Proof sketch

Once $Z_j$ is small, squaring at a constant fraction of the steps (the $+$ steps, about half of them by the law of large numbers) and at most doubling at the others makes $\log_2(1/Z_n)$ grow like $2^{n/2 - o(n)} = N^{1/2 - o(1)}$. A bootstrapping argument first brings $Z_j$ below a small constant on a set of probability close to $I(W)$ using almost sure convergence, then applies the squaring dynamics. For the converse, $Z(W^{+}) = Z(W)^2$ and $Z(W^{-}) \ge Z(W)$, so $\log_2(1/Z_n)$ at most doubles at each step and only at the $+$ steps; starting from $Z(W) > 0$, which is where $I(W) < 1$ enters, it is at most $2^{n/2 + o(n)} \log_2(1/Z(W))$ for most paths.

## Depends on

- [Binary memoryless symmetric channels, symmetric capacity and the Bhattacharyya parameter](bhattacharyya-parameter-and-symmetric-capacity.md)
- [Synthesized polar subchannels](synthesized-polar-subchannels.md)

## Proof depends on

- [The polarization martingale](polarization-martingale.md)

## Sources

- Erdal Arikan, Emre Telatar, "On the rate of channel polarization", ISIT (2009); arXiv:0807.3806.
- Satish Babu Korada, Eren Sasoglu, Rudiger Urbanke, "Polar codes: characterization of exponent, bounds, and constructions", IEEE Transactions on Information Theory 56(12) (2010); arXiv:0901.0536, Theorem 14 and Lemma 21.
