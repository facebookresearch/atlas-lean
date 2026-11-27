# Bhattacharyya recursion under one polarization step

For every BMS channel $W$, the channels $W^{-}, W^{+}$ are BMS and

$$
Z(W^{+}) = Z(W)^2, \qquad Z(W) \le Z(W^{-}) \le 2Z(W) - Z(W)^2,
$$

while $I(W^{-}) + I(W^{+}) = 2I(W)$ and $I(W^{-}) \le I(W) \le I(W^{+})$. For the binary erasure channel with erasure probability $\epsilon$, $W^{-}$ and $W^{+}$ are erasure channels with parameters $2\epsilon - \epsilon^2$ and $\epsilon^2$.

## Proof sketch

$W^{+}$ observes two independent copies of $W$ applied to $u_2$ (after removing the known $u_1$), so its Bhattacharyya parameter is the product $Z(W)^2$. For $W^{-}$, the bit $u_1$ is seen through $u_1 \oplus u_2$ and $u_2$ with $u_2$ uniform; a direct computation with the Cauchy-Schwarz inequality gives the upper bound and a degradation argument the lower bound. Conservation of mutual information is the chain rule applied to $(u_1, u_2) \mapsto (u_1 \oplus u_2, u_2)$, a bijection.

## Depends on

- [Synthesized polar subchannels](synthesized-polar-subchannels.md)
- [Binary memoryless symmetric channels, symmetric capacity and the Bhattacharyya parameter](bhattacharyya-parameter-and-symmetric-capacity.md)

## Proof depends on

- [Polar transform: channel combining/splitting conservation](../polar-transform-channel-combining-splitting-conservation.md)

## Sources

- Erdal Arikan, "Channel polarization: a method for constructing capacity-achieving codes for symmetric binary-input memoryless channels", IEEE Transactions on Information Theory 55(7) (2009); arXiv:0807.3917.
