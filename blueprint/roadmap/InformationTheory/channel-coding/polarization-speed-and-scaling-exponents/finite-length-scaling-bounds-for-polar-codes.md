# Hassani-Alishahi-Urbanke and Mondelli-Hassani-Urbanke: bounds on the polar scaling exponent

For polar codes with Arikan's kernel under successive cancellation decoding, the scaling exponent $\mu$ satisfies $3.579 \le \mu \le 6$ universally over BMS channels (Hassani-Alishahi-Urbanke), and the upper bound improves to $\mu \le 4.714$ for every BMS channel (Mondelli-Hassani-Urbanke).

## Proof sketch

Track the number of subchannels whose Bhattacharyya parameter lies in a fixed interval $[a, b]$: it decays like $N^{1 - 1/\mu}$ for some exponent controlled by the eigenvalue of a linear operator acting on functions of $Z$, obtained from the recursion $Z \mapsto (Z^2, 2Z - Z^2)$ (exact for the erasure channel and a bound in general). Upper and lower bounds follow from functional inequalities for this operator evaluated on test functions like $(z(1-z))^{\alpha}$.

## Depends on

- [Scaling exponent of polar codes](scaling-exponent-of-a-code-family.md)
- [Binary memoryless symmetric channels, symmetric capacity and the Bhattacharyya parameter](bhattacharyya-parameter-and-symmetric-capacity.md)
- [Polar codes and successive cancellation decoding](polar-codes-and-successive-cancellation-decoding.md)

## Proof depends on

- [Bhattacharyya recursion under one polarization step](bhattacharyya-recursion-under-the-polar-transform.md)

## Sources

- S. Hamed Hassani, Kasra Alishahi, Rudiger Urbanke, "Finite-length scaling for polar codes", IEEE Transactions on Information Theory 60(10) (2014); arXiv:1304.4778.
- Marco Mondelli, S. Hamed Hassani, Rudiger Urbanke, "Unified scaling of polar codes: error exponent, scaling exponent, moderate deviations, and error floors", IEEE Transactions on Information Theory 62(12) (2016); arXiv:1501.02444.
