# Statistical error of finite-width fixed-weight sampling

Let $w \le n < 2^b$. For every fixed-weight support $S$, the probability that the finite-width HQC sampler (SampleFixedWeightVect, drawing one $b$-bit word per position) outputs $S$ is sandwiched between $L \cdot \binom{n}{w}^{-1}$ and $U \cdot \binom{n}{w}^{-1}$, where $L = \prod_{i<w} \lfloor 2^b/(n-i) \rfloor (n-i)/2^b$ and $U = \prod_{i<w} (\lfloor 2^b/(n-i)\rfloor + 1)(n-i)/2^b$ are products of per-word floor-count density factors. These are the bounds $\tau_{\min}^{w} = \prod_{i<w}(1 - n_i/2^b)$ and $\tau_{\max}^{w} = \prod_{i<w}\bigl(1 + ((n-i) - n_i)/2^b\bigr)$, with $n_i = 2^b \bmod (n-i)$, of the HQC specification (Section 6.2.3, Proposition 6.2.1) on the ratio to the specification's rejection-sampling variant of the sampler, whose output is uniform on weight-$w$ vectors (Section 3.3). Consequently, for every nonnegative payoff function $f$, $\mathbb{E}_{\mathrm{sampler}}[f] \le U\,\mathbb{E}_{\mathrm{ideal}}[f]$ (Lemma 6.5).

## Proof sketch

The $i$-th word lands on each value of its interval $[i, n)$ for either $\lfloor 2^b/(n-i)\rfloor$ or that number plus one of the $2^b$ word values. The descending correction maps the $\prod_{i<w}(n-i) = w!\binom{n}{w}$ candidate sequences onto the weight-$w$ supports, exactly $w!$ of them onto each support, as in Floyd's algorithm; it is not a bijection onto ordered supports (for $n = 3$, $w = 2$ the candidate sequences $(0,1)$ and $(1,1)$ both give $\{0,1\}$). So the probability of each support is a sum of $w!$ products of these counts, which gives the sandwich. The lower half also gives $\mathbb{E}_{\mathrm{sampler}}[f] \ge L\,\mathbb{E}_{\mathrm{ideal}}[f]$ for nonnegative $f$, and the statistical distance from the uniform law on weight-$w$ vectors is $\sum_S (u(S) - p(S))^+ \le (1 - L)\sum_S u(S) = 1 - L$; since $\prod_i (1 - x_i) \ge 1 - \sum_i x_i$ for $x_i \in [0,1]$, $1 - L \le \sum_{i<w} n_i/2^b \le \sum_{i<w} (n-i)/2^b$.

## Depends on

- [Fixed-weight support sampling in HQC](hqc-fixed-weight-sampling.md)

## Sources

- Philippe Gaborit et al., "Hamming Quasi-Cyclic (HQC)", Version 5.1, November 9, 2026, Section 3.3 and Section 6.2.3, Proposition 6.2.1 and Lemma 6.5.
