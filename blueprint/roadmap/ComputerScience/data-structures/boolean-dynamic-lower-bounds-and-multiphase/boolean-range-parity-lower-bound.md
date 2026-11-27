# Larsen–Weinstein–Yu: super-logarithmic lower bound for range parity

Every dynamic cell-probe structure for two-dimensional range parity with cell size $w$, worst-case update time $t_u$ and expected query time $t_q$ satisfies

$$
t_q = \Omega\!\left(\frac{\lg^{3/2} n}{\lg^{3}(t_u w)}\right)
$$

(Corollary 1); in particular, with $w = \Theta(\lg n)$ and $t_u = (\lg n)^{O(1)}$, $t_q = \tilde{\Omega}(\lg^{1.5} n)$, where $\tilde{\Omega}$ hides $(\lg\lg n)^{O(1)}$ factors. Similar bounds hold for Boolean dynamic polynomial evaluation and two-dimensional rectangle stabbing, and for range selection and range median; the bound implies the first $\omega(\lg n)$ lower bound for classical two-dimensional range counting.

## Proof sketch

Larsen, Weinstein and Yu split the random insertions into epochs and simulate the dynamic structure *weakly* (Theorem 1): for some epoch $i$, a one-way protocol in which Alice sends $|\mathbf{U}_i|/(w t_u)^{\Theta(1)}$ bits, a random sample of the cells associated with the epoch, lets Bob answer a random query with advantage $\exp(-t_q \lg^2(w t_u)/\sqrt{\lg n})$ over random guessing. The advantage bound comes from their peak-to-average lemma, proved with discrete Chebyshev polynomials. They prove the lower bound for parity searching in Butterfly graphs, whose answers are list-decodable enough that such an advantage would reveal too much information about the epoch, and reduce that problem to two-dimensional range parity (Theorem 4).

## Depends on

- [Dynamic two-dimensional range parity](range-parity-problem.md)
- [The cell-probe model](../range-query-structures/advanced-data-structures/the-cell-probe-model.md)

## Proof depends on

- [Cell-sampling lemma](../cell-sampling-and-range-counting-lower-bounds/cell-sampling-lemma.md)

## Sources

- Kasper Green Larsen, Omri Weinstein, Huacheng Yu, "Crossing the Logarithmic Barrier for Dynamic Boolean Data Structure Lower Bounds", STOC (2018); SIAM Journal on Computing (2020), arXiv:1703.03575.
