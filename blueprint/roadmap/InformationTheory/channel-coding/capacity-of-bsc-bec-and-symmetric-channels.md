# Capacity of BSC, BEC and symmetric channels

For the binary symmetric channel with crossover probability $\delta \in [0,1]$ and the binary erasure channel with erasure
probability $\varepsilon \in [0,1]$, the maximum of $I(X;Y)$ over input distributions is $1 - h(\delta)$ and
$1 - \varepsilon$ bits respectively, attained by the uniform input. More generally, for a weakly symmetric channel with finite input and output alphabets (rows are
permutations of each other and column sums are equal) the uniform input maximizes $I(X;Y)$, with value
$\log_2 \lvert Y \rvert - H(\text{row})$ bits. The equality of this maximum with the operational capacity is Shannon's channel
coding theorem, a separate result.

## Proof of the weakly symmetric clause

Let the channel $W(y \mid x)$ have finite input alphabet $\mathcal{X}$ and finite output alphabet $Y$. Every row
$W(\cdot \mid x)$ is a permutation of the first, so $H(Y \mid X = x) = H(\text{row})$ for every $x$, and
$I(X; Y) = H(Y) - H(\text{row}) \le \log_2 \lvert Y \rvert - H(\text{row})$ for every input law. Each column sum equals
$\lvert \mathcal{X} \rvert / \lvert Y \rvert$, so the uniform input gives the output law
$P(y) = \frac{1}{\lvert \mathcal{X} \rvert} \sum_x W(y \mid x) = 1/\lvert Y \rvert$, which attains $H(Y) = \log_2 \lvert Y \rvert$.

## Depends on

- [Mutual information of a finite joint law](../entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md)

## Related topics

- [Weak converse for discrete memoryless channels](shannon-s-channel-coding-theorem/channel-coding-weak-converse.md)
- [Shannon's channel coding theorem, achievability](shannon-s-channel-coding-theorem/channel-coding-achievability.md)

## Sources

- Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press, 2025 (author draft),
  Section 19.3 (BSC: $C = \log 2 - h(\delta)$; BEC: $C = 1 - \delta$ bits); the weakly symmetric clause is derived above. <https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf>
