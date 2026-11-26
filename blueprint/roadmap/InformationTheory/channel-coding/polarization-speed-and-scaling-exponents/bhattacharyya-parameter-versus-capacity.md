# Bhattacharyya parameter versus symmetric capacity

For every BMS channel $W$,

$$
I(W) \ge \log_2 \frac{2}{1 + Z(W)} \qquad \text{and} \qquad I(W) \le \sqrt{1 - Z(W)^2} .
$$

In particular $I(W) \to 1$ if and only if $Z(W) \to 0$, and $I(W) \to 0$ if and only if $Z(W) \to 1$.

## Proof sketch

The first inequality is the Rényi-entropy (order $1/2$) lower bound on mutual information: $I(W) \ge -\log_2 \sum_y \big(\tfrac12\sqrt{W(y|0)} + \tfrac12\sqrt{W(y|1)}\big)^2 = \log_2\frac{2}{1+Z}$. For the second, decompose the BMS channel as a mixture of binary symmetric channels; for a BSC both quantities are explicit functions of the crossover probability and the inequality is checked directly, then extended by concavity of $\sqrt{1 - z^2}$.

## Depends on

- [Binary memoryless symmetric channels, symmetric capacity and the Bhattacharyya parameter](bhattacharyya-parameter-and-symmetric-capacity.md)

## Sources

- Erdal Arikan, "Channel polarization: a method for constructing capacity-achieving codes for symmetric binary-input memoryless channels", IEEE Transactions on Information Theory 55(7) (2009); arXiv:0807.3917.
