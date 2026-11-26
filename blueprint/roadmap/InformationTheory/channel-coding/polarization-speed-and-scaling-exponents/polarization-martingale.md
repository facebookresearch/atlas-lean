# The polarization martingale

Let $B_1, B_2, \dots$ be independent uniform bits and define the random channel process $W_0 = W$, $W_{j+1} = W_j^{-}$ if $B_{j+1} = 0$ and $W_j^{+}$ otherwise. Then $I_j = I(W_j)$ is a bounded martingale and $Z_j = Z(W_j)$ is a bounded supermartingale with respect to the filtration of $B_1, \dots, B_j$; both converge almost surely, and the limits satisfy $I_\infty \in \{0, 1\}$ and $Z_\infty = 1 - I_\infty$ almost surely, with $\Pr[I_\infty = 1] = I(W)$.

## Proof sketch

Conservation of mutual information gives the martingale property, and the recursion bounds $\mathbb{E}[Z_{j+1} \mid Z_j] \le \frac12(Z_j^2 + 2Z_j - Z_j^2) = Z_j$. Bounded martingales converge almost surely, so $|Z_{j+1} - Z_j| \to 0$; since $Z_{j+1} = Z_j^2$ with probability $1/2$, every limit point satisfies $z = z^2$, so $Z_\infty \in \{0, 1\}$, and the capacity-Bhattacharyya inequalities force $I_\infty = 1 - Z_\infty$. Taking expectations, $\Pr[I_\infty = 1] = \mathbb{E}I_\infty = I(W)$.

## Depends on

- [Binary memoryless symmetric channels, symmetric capacity and the Bhattacharyya parameter](bhattacharyya-parameter-and-symmetric-capacity.md)
- [Synthesized polar subchannels](synthesized-polar-subchannels.md)

## Proof depends on

- [Bhattacharyya recursion under one polarization step](bhattacharyya-recursion-under-the-polar-transform.md)
- [Bhattacharyya parameter versus symmetric capacity](bhattacharyya-parameter-versus-capacity.md)

## Sources

- Erdal Arikan, "Channel polarization: a method for constructing capacity-achieving codes for symmetric binary-input memoryless channels", IEEE Transactions on Information Theory 55(7) (2009); arXiv:0807.3917.
