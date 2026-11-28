# Learning-rate weights of optimistic Q-learning

For the learning rate $\alpha_t = (H+1)/(H+t)$, the weights $\alpha_t^i$ that $t$ incremental updates put on the $i$-th target sum to one, satisfy $1/\sqrt t \le \sum_i \alpha_t^i/\sqrt i \le 2/\sqrt t$, have largest weight and sum of squares at most $2H/t$, and give every fixed $i$ a total weight $\sum_{t \ge i} \alpha_t^i = 1 + 1/H$ over all later $t$.

Let $H \ge 1$ and $\alpha_t = (H+1)/(H+t)$ for integers $t \ge 1$, and put

$$
\alpha_t^0 = \prod_{j=1}^{t} (1 - \alpha_j), \qquad \alpha_t^i = \alpha_i \prod_{j=i+1}^{t} (1 - \alpha_j) \quad (1 \le i \le t).
$$

Then $\alpha_t^0 = 0$ and $\sum_{i=1}^t \alpha_t^i = 1$ for $t \ge 1$, while $\alpha_0^0 = 1$ with an empty sum, and:

1. $\dfrac{1}{\sqrt t} \le \displaystyle\sum_{i=1}^{t} \frac{\alpha_t^i}{\sqrt i} \le \frac{2}{\sqrt t}$ for every $t \ge 1$;
2. $\displaystyle\max_{1 \le i \le t} \alpha_t^i \le \frac{2H}{t}$ and $\displaystyle\sum_{i=1}^{t} (\alpha_t^i)^2 \le \frac{2H}{t}$ for every $t \ge 1$;
3. $\displaystyle\sum_{t=i}^{\infty} \alpha_t^i = 1 + \frac{1}{H}$ for every $i \ge 1$.

## Depends on

None.

## Proof depends on

None.

## Expansion

Since $\alpha_1 = 1$, the product defining $\alpha_t^0$ vanishes for $t \ge 1$, and the weights telescope to one. For item 3, $\alpha_t^i = \frac{H+1}{i+H}\prod_{j=i+1}^{t}\frac{j-1}{H+j}$, and the series $\sum_{t \ge i}$ evaluates to $\frac{H+1}{i+H}\cdot\frac{i+H}{H} = \frac{H+1}{H}$ by the identity (B.1) of the source with $n = i + H$ and $k = H$. Item 1 follows by induction on $t$ from $\alpha_t^i = (1 - \alpha_t)\alpha_{t-1}^i$ for $i < t$, using $H \ge 1$. For item 2, rearranging the product gives $\alpha_t^i \le (H+1)/(t+H) \le 2H/t$, and then $\sum_i (\alpha_t^i)^2 \le \max_i \alpha_t^i \cdot \sum_i \alpha_t^i$.

The weights are those of the [optimistic Q-learning](optimistic-q-learning-with-ucb-bonuses.md) update: after $t$ visits to a triple $(x, a, h)$ the stored value is $\alpha_t^0 H$ plus the $\alpha_t^i$-weighted average of the $t$ targets. Item 3 is what keeps error propagation polynomial: in the regret recursion each stage multiplies the error carried from the next stage by at most $\sum_{t \ge i} \alpha_t^i$, and $(1 + 1/H)^H \le e$. Item 1 turns the bonus $c\sqrt{H^3\iota/t}$ into an accumulated bonus $2\sum_i \alpha_t^i b_i$ between $2c\sqrt{H^3\iota/t}$ and $4c\sqrt{H^3\iota/t}$, and item 2 controls the Azuma–Hoeffding deviation of the weighted average of next-state values by $\sqrt{H^3\iota/t}$ up to a constant.

## Sources

- C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, "Is Q-learning Provably Efficient?", *Advances in Neural Information Processing Systems 31* (NeurIPS 2018), the weights (4.2), the facts stated after them, and Lemma 4.1; proof in Appendix B of the full version arXiv:1807.03765v1, including the identity (B.1). [PDF](https://proceedings.neurips.cc/paper_files/paper/2018/file/d3b1fb02964aa64e257f9f26a31f72cf-Paper.pdf)
