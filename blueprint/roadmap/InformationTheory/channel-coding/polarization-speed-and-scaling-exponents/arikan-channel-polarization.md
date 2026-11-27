# Arikan's channel polarization theorem

For every BMS channel $W$ and every $\delta \in (0, 1)$,

$$
\lim_{N \to \infty} \frac{\#\{i \le N : I(W_N^{(i)}) > 1 - \delta\}}{N} = I(W), \qquad \lim_{N \to \infty} \frac{\#\{i \le N : I(W_N^{(i)}) < \delta\}}{N} = 1 - I(W),
$$

where $N = 2^n \to \infty$.

## Proof sketch

A uniformly random index $i \le 2^n$ corresponds to a uniformly random path $B_1, \dots, B_n$, so the fraction of indices with $I(W_N^{(i)}) > 1 - \delta$ is $\Pr[I_n > 1 - \delta]$. Almost sure convergence of the polarization martingale to $\{0,1\}$ with $\Pr[I_\infty = 1] = I(W)$ gives the limits.

## Depends on

- [Binary memoryless symmetric channels, symmetric capacity and the Bhattacharyya parameter](bhattacharyya-parameter-and-symmetric-capacity.md)
- [Synthesized polar subchannels](synthesized-polar-subchannels.md)

## Proof depends on

- [The polarization martingale](polarization-martingale.md)

## Sources

- Erdal Arikan, "Channel polarization: a method for constructing capacity-achieving codes for symmetric binary-input memoryless channels", IEEE Transactions on Information Theory 55(7) (2009); arXiv:0807.3917.
