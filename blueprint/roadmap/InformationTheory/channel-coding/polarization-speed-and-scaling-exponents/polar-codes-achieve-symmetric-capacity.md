# Polar codes achieve the capacity of BMS channels

For every BMS channel $W$, every rate $R < I(W)$ and every $\beta < 1/2$, polar codes of length $N = 2^n$ and rate at least $R$ have block error probability $O(2^{-N^{\beta}})$ under successive cancellation decoding, with encoding and decoding complexity $O(N \log N)$.

## Proof sketch

By the rate-of-polarization theorem at least $RN$ indices satisfy $Z(W_N^{(i)}) \le 2^{-N^{\beta'}}$ for $\beta < \beta' < 1/2$ and large $N$. Choosing them as the information set, the union bound on the successive cancellation error gives at most $N \cdot 2^{-N^{\beta'}} = O(2^{-N^{\beta}})$.

## Depends on

- [Polar codes and successive cancellation decoding](polar-codes-and-successive-cancellation-decoding.md)
- [Binary memoryless symmetric channels, symmetric capacity and the Bhattacharyya parameter](bhattacharyya-parameter-and-symmetric-capacity.md)

## Proof depends on

- [Arikan-Telatar: rate of polarization](rate-of-channel-polarization.md)
- [Shannon's channel coding theorem, achievability](../shannon-s-channel-coding-theorem/channel-coding-achievability.md)

## Sources

- Erdal Arikan, "Channel polarization: a method for constructing capacity-achieving codes for symmetric binary-input memoryless channels", IEEE Transactions on Information Theory 55(7) (2009); arXiv:0807.3917.
- Erdal Arikan, Emre Telatar, "On the rate of channel polarization", ISIT (2009); arXiv:0807.3806.
