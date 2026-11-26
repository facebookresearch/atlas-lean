# Hassani-Alishahi-Urbanke and Mondelli-Hassani-Urbanke: bounds on the polar scaling exponent

Consider polar codes with Arikan's kernel under successive cancellation (SC) decoding on a BMS channel $W$ with $I(W) \in (0, 1)$, block length $N$ and rate $R$, and let the information set be chosen by the polar construction.

- *Converse (Hassani-Alishahi-Urbanke, Theorem 16).* There are $P_e, \alpha > 0$ depending only on $I(W)$ such that if the sum of the bit-error probabilities of the synthesized subchannels in the information set is at most $P_e$, then $R < I(W) - \alpha N^{-1/\mu}$ with $\mu = 3.579$. This hypothesis is on the sum, not on the SC block error probability: the sum bounds the block error probability from above, but a small block error probability does not make the sum small, so the converse does not directly bound block-error scaling.
- *Achievability.* Hassani-Alishahi-Urbanke show that the same sum criterion, with Bhattacharyya parameters, can be met at rates $I(W) - \beta N^{-1/6}$. Mondelli-Hassani-Urbanke show that for every BMS channel the SC block error probability can be kept at most a given $P_e$ at rates $I(W) - \beta N^{-1/\mu}$ with $\mu = 4.714$, where $\beta$ depends on $P_e$ and $I(W)$.

## Proof sketch

Track the number of subchannels whose Bhattacharyya parameter (or entropy) lies in a fixed interval $[a, b]$: it decays like $N^{1 - 1/\mu}$ for an exponent controlled by the eigenvalue of a linear operator acting on functions of $Z$, obtained from the recursion $Z \mapsto (Z^2, 2Z - Z^2)$ (exact for the erasure channel and a bound in general). The converse lower-bounds $\mathbb{E}[H_n(1-H_n)]$ through test functions such as $h(1-h)$ and turns many unpolarized subchannels into a large sum of bit-error probabilities; the upper bounds evaluate the operator on test functions like $(z(1-z))^{\alpha}$ and then bound the block error probability by the sum of Bhattacharyya parameters.

## Depends on

- [Scaling exponent of polar codes](scaling-exponent-of-a-code-family.md)
- [Binary memoryless symmetric channels, symmetric capacity and the Bhattacharyya parameter](bhattacharyya-parameter-and-symmetric-capacity.md)
- [Polar codes and successive cancellation decoding](polar-codes-and-successive-cancellation-decoding.md)

## Proof depends on

- [Bhattacharyya recursion under one polarization step](bhattacharyya-recursion-under-the-polar-transform.md)

## Sources

- S. Hamed Hassani, Kasra Alishahi, Rudiger Urbanke, "Finite-length scaling for polar codes", IEEE Transactions on Information Theory 60(10) (2014); arXiv:1304.4778.
- Marco Mondelli, S. Hamed Hassani, Rudiger Urbanke, "Unified scaling of polar codes: error exponent, scaling exponent, moderate deviations, and error floors", IEEE Transactions on Information Theory 62(12) (2016); arXiv:1501.02444.
