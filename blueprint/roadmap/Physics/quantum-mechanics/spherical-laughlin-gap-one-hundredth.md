# Spherical Laughlin gap bound with coefficient one hundredth

At flux $Q=3(N-1)$, use tensors $\psi(a)$ indexed by $a\in\{0,\dots,Q\}^N$ that change sign under swaps of distinct particle positions. Put $[Q]_k=Q(Q-1)\cdots(Q-k+1)$ with $[Q]_0=1$. Define $b_{Qp}(x,y)=0$ unless $x+y=p+1$, in which case

$$
b_{Qp}(x,y)=\frac{x-y}{\sqrt2}\sqrt{\frac{[Q]_x[Q]_y p!}{Q[2Q-2]_p x!y!}}.
$$

The energy $\mathcal E_Q$ is the sum over $i<j$, $0\leq p<2Q-1$, and assignments of the other particles, of the squared modulus of $\sum_{x,y} b_{Qp}(x,y)\psi(a_{i\gets x,j\gets y})$. Define $L_Q(a)$ by taking the coefficient of $\prod_i u_i^{Q-a_i}v_i^{a_i}$ in $\prod_{i<j}(u_iv_j-u_jv_i)^3$ and dividing it by $\prod_i\sqrt{\binom Q{a_i}}$. There exists $N_0\geq2$ such that for every $N\geq N_0$ and all antisymmetric $\psi$, $\mathcal E_Q(\psi)\geq(1/100)\inf_{c\in\mathbb C}\sum_a|\psi(a)-cL_Q(a)|^2$.

## Depends on
The specified coefficient tensor, the weight converting polynomial coefficients to the orbital basis, and the squared Euclidean distance to the complex span.

## Proof depends on
- [Stronger gap with coefficient one twenty-fifth](spherical-laughlin-gap-one-twenty-fifth.md), which implies the weaker bound by nonnegativity of squared distance.

## Proof strategy
Identify the two comparator orbital models and justify monotonicity in the gap coefficient on the nonnegative squared-distance infimum. This bound is unperturbed.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Laughlin.lean#L61-L63) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/269.md).
