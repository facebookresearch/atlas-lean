# Polar codes and successive cancellation decoding

For $N = 2^n$, a rate $R$ and a BMS channel $W$, the *polar code* with information set $\mathcal{A} \subseteq [N]$ of size $RN$ chosen as the indices with the smallest $Z(W_N^{(i)})$ encodes $u_{\mathcal{A}}$ (with $u_{\mathcal{A}^c} = 0$ frozen) as $x = u G_N$. The *successive cancellation decoder* computes, for $i = 1, \dots, N$, $\hat u_i = 0$ if $i \notin \mathcal{A}$ and otherwise the maximum-likelihood value of $u_i$ under $W_N^{(i)}$ given $y$ and $\hat u_1^{i-1}$, in total time $O(N \log N)$ by the recursive structure of $G_N$. Its block error probability is at most $\sum_{i \in \mathcal{A}} Z(W_N^{(i)})$.

## Depends on

- [Synthesized polar subchannels](synthesized-polar-subchannels.md)

## Sources

- Erdal Arikan, "Channel polarization: a method for constructing capacity-achieving codes for symmetric binary-input memoryless channels", IEEE Transactions on Information Theory 55(7) (2009); arXiv:0807.3917.
