# XOR lemma for statistical distance

For distributions $p_0, p_1$ on a finite set and every $k \ge 1$,

$$
\delta\big(\mathrm{XOR}_k(p_0, p_1; 0),\ \mathrm{XOR}_k(p_0, p_1; 1)\big) = \delta(p_0, p_1)^k .
$$

Indeed, for every $x \in X^k$ the two masses differ by exactly $2^{-(k-1)}\prod_{i=1}^k\big(p_0(x_i) - p_1(x_i)\big)$.

## Proof sketch

Expanding the parity-restricted averages as $\frac{1}{2^{k}}\sum_b (1 \pm (-1)^{\oplus b})\prod_i p_{b_i}(x_i)$, the difference of the two masses is $2^{-(k-1)}\sum_b (-1)^{\oplus b}\prod_i p_{b_i}(x_i) = 2^{-(k-1)}\prod_i (p_0(x_i) - p_1(x_i))$. Summing absolute values over $x$ factors over coordinates into $2^{-(k-1)}(2\delta)^k$, and halving gives $\delta^k$.

## Depends on

- [XOR construction of two distributions](xor-construction.md)
- [Total variation distance between finite measures](../../convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- A. Sahai and S. Vadhan, "A Complete Problem for Statistical Zero Knowledge", Journal of the ACM 50(2), 2003.
