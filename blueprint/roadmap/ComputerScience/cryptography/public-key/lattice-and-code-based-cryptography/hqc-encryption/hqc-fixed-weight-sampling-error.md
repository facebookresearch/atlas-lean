# Statistical error of finite-width fixed-weight sampling

Let $w \le n < 2^b$. For every fixed-weight support $S$, the probability that the finite-width HQC sampler outputs $S$ is sandwiched between $L \cdot \binom{n}{w}^{-1}$ and $U \cdot \binom{n}{w}^{-1}$, where $L = \prod_{i<w} \lfloor 2^b/(n-i) \rfloor (n-i)/2^b$ and $U = \prod_{i<w} (\lfloor 2^b/(n-i)\rfloor + 1)(n-i)/2^b$ are products of per-word floor-count density factors. Consequently, for every nonnegative payoff function $f$, $L\,\mathbb{E}_{\mathrm{ideal}}[f] \le \mathbb{E}_{\mathrm{sampler}}[f] \le U\,\mathbb{E}_{\mathrm{ideal}}[f]$, and the sampler's output law is within statistical distance $1 - L \le \sum_{i<w} (n-i)/2^b$ of the uniform law on weight-$w$ vectors. The sampler always returns a support of the requested size, and it is computed by a Boolean circuit of size polynomial in $w$, $b$ and $\log n$.

## Proof sketch

Each word lands on any given position of its interval for either $\lfloor 2^b/(n-i)\rfloor$ or that number plus one of the $2^b$ word values; the descending correction is a bijection from candidate sequences onto ordered supports, so the probability of each support is a product of these counts.

## Depends on

- [Fixed-weight support sampling in HQC](hqc-fixed-weight-sampling.md)

## Sources

- Philippe Gaborit et al., "Hamming Quasi-Cyclic (HQC)", Version 5.1, November 9, 2026.
