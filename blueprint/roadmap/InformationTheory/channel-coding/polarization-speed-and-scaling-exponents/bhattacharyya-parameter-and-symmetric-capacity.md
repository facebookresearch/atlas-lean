# Binary memoryless symmetric channels, symmetric capacity and the Bhattacharyya parameter

A *binary-input memoryless symmetric (BMS) channel* $W : \{0,1\} \to \mathcal{Y}$ is a transition kernel $W(y \mid x)$ with finite (or countable) output alphabet admitting an involution $\pi$ of $\mathcal{Y}$ with $W(y \mid 1) = W(\pi(y) \mid 0)$. Its *symmetric capacity* is

$$
I(W) = \sum_{y}\sum_{x \in \{0,1\}} \tfrac12 W(y \mid x) \log_2 \frac{W(y \mid x)}{\tfrac12 W(y \mid 0) + \tfrac12 W(y \mid 1)},
$$

which equals its Shannon capacity, and its *Bhattacharyya parameter* is $Z(W) = \sum_y \sqrt{W(y \mid 0)\, W(y \mid 1)} \in [0,1]$, an upper bound on the error probability of maximum-likelihood decoding of one uniformly random bit.

## Depends on

- [Capacity of BSC, BEC and symmetric channels](../capacity-of-bsc-bec-and-symmetric-channels.md)

## Sources

- Erdal Arikan, "Channel polarization: a method for constructing capacity-achieving codes for symmetric binary-input memoryless channels", IEEE Transactions on Information Theory 55(7) (2009); arXiv:0807.3917.
