# Expected cost of a pure strategy against mixed opponents

For real weights $\sigma_l : S_l \to \mathbb{R}$ (mixed strategies in the intended use), the expected cost of the pure strategy $a$ of player $i$ when the others play
$\sigma_l$ independently is

$$\bar c_i(a) = \sum_{s :\, s_i = a} \Bigl(\prod_{l \ne i} \sigma_l(s_l)\Bigr) c_i(s).$$
