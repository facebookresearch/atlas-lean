# Uniform tuples are good samplers

Let $U$ be a nonempty finite set, $I$ a finite index set, and $F : U \to [0,1]$ with $\frac{1}{|U|}\sum_{x}F(x) \ge \mu$, where $0 \le \mu \le 1$. Then the number of tuples $b \in U^I$ with $\sum_{i \in I}F(b_i) \le \mu|I|/2$ is at most $|U|^{|I|}\, e^{-\mu|I|/8}$. Consequently, for every family $W \subseteq U^I$ of tuples,

$$
\Big(|W| - |U|^{|I|}e^{-\mu|I|/8}\Big)\,\mu|I| \le 2\sum_{b \in W}\sum_{i \in I}F(b_i).
$$

## Proof sketch

The first claim is the multiplicative Chernoff lower tail at relative deviation $1/2$, stated by counting uniformly random tuples. For the second, all but at most $|U|^{|I|}e^{-\mu|I|/8}$ tuples of $W$ have $\sum_i F(b_i) > \mu|I|/2$, and the remaining summands are nonnegative.

## Proof depends on

- [Multiplicative Chernoff bounds for independent [0,1]-valued scores](../../concentration-inequalities/chernoff-and-bernoulli-comparison-bounds/multiplicative-chernoff-bounds.md)

## Sources

- R. Impagliazzo, R. Jaiswal, V. Kabanets and A. Wigderson, "Uniform Direct Product Theorems: Simplified, Optimized, and Derandomized", SIAM Journal on Computing, 2010.
- M. Mitzenmacher and E. Upfal, "Probability and Computing: Randomization and Probabilistic Techniques in Algorithms and Data Analysis", Cambridge University Press, 2nd ed., 2017.
