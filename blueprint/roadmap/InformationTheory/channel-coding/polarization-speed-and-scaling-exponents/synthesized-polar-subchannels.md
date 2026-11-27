# Synthesized polar subchannels

Let $N = 2^n$, $F = \begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$ and $G_N = B_N F^{\otimes n}$ with $B_N$ the bit-reversal permutation. For a BMS channel $W$, the combined channel $W_N(y_1^N \mid u_1^N) = \prod_{i=1}^{N} W(y_i \mid (u_1^N G_N)_i)$ is split into $N$ *synthesized subchannels*

$$
W_N^{(i)}(y_1^N, u_1^{i-1} \mid u_i) = \sum_{u_{i+1}^N} \frac{1}{2^{N-1}} W_N(y_1^N \mid u_1^N), \qquad 1 \le i \le N,
$$

in which bit $u_i$ is transmitted while earlier bits are known to the receiver and later bits are uniformly random. One step of the recursion maps a pair of copies of $W$ to $W^{-} = W_2^{(1)}$ and $W^{+} = W_2^{(2)}$.

## Depends on

- [Binary memoryless symmetric channels, symmetric capacity and the Bhattacharyya parameter](bhattacharyya-parameter-and-symmetric-capacity.md)
- [Polar transform: channel combining/splitting conservation](../polar-transform-channel-combining-splitting-conservation.md)

## Sources

- Erdal Arikan, "Channel polarization: a method for constructing capacity-achieving codes for symmetric binary-input memoryless channels", IEEE Transactions on Information Theory 55(7) (2009); arXiv:0807.3917.
