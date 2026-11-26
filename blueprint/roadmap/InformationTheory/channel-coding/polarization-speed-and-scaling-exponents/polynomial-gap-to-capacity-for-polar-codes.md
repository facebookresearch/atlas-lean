# Guruswami-Xia: polar codes have polynomial gap to capacity

There is an absolute constant $\mu < \infty$ such that for every BMS channel $W$ and every $\varepsilon > 0$, polar codes of block length $N = \mathrm{poly}(1/\varepsilon)$, specifically $N = O\big((1/\varepsilon)^{\mu}\big)$, achieve rate $I(W) - \varepsilon$ with block error probability at most $2^{-N^{0.49}}$ under successive cancellation decoding, and can be constructed in time $\mathrm{poly}(N)$. Equivalently, the scaling exponent of polar codes is finite uniformly over all BMS channels.

## Proof sketch

Quantify the martingale convergence: for the potential $T_j = \sqrt{Z_j(1 - Z_j)}$ show $\mathbb{E}[T_{j+1} \mid T_j] \le \Lambda\, T_j$ with $\Lambda < 1$ absolute, so the fraction of unpolarized indices decays as $\Lambda^{n} = N^{-\Omega(1)}$. A second phase uses rapid squaring to drive the Bhattacharyya parameters of good indices to $2^{-N^{0.49}}$. Efficient construction uses channel output-alphabet degradation and upgradation to approximate the subchannels.

## Depends on

- [Scaling exponent of polar codes](scaling-exponent-of-a-code-family.md)
- [Binary memoryless symmetric channels, symmetric capacity and the Bhattacharyya parameter](bhattacharyya-parameter-and-symmetric-capacity.md)
- [Polar codes and successive cancellation decoding](polar-codes-and-successive-cancellation-decoding.md)

## Proof depends on

- [Polar codes achieve the capacity of BMS channels](polar-codes-achieve-symmetric-capacity.md)

## Sources

- Venkatesan Guruswami, Patrick Xia, "Polar codes: speed of polarization and polynomial gap to capacity", IEEE Transactions on Information Theory 61(1) (2015), FOCS (2013).
