# Berry–Esseen rates for the Yule–Ornstein–Uhlenbeck trait average

**Model (YOU).** A phenotypic trait evolves along the branches of a pure-birth (Yule) tree with birth rate $1$, stopped just before the $n$-th speciation event, so that it has $n$ tips. Along each branch the trait follows the Ornstein–Uhlenbeck process $dX=-\alpha X\,dt+\sigma_a\,dW$ with $\alpha,\sigma_a>0$.

At a speciation the process is copied into both daughter lineages, which then evolve independently. Let $\overline X_n$ be the average trait over the $n$ tips. Rescale by $\overline Y_n=\overline X_n\sqrt{2\alpha/\sigma_a^2}$ and $\delta=X(0)\sqrt{2\alpha/\sigma_a^2}$. Let $\mathscr G$ be the $\sigma$-algebra of the tree, and put $\mu_n=\mathbb E\overline Y_n$ and $\sigma_n^2=\mathbb E\,\mathbb V(\overline Y_n\mid\mathscr G)$. Write $H_n=\sum_{j\le n}1/j$ and $b_{n,x}=\prod_{j=1}^n\frac{j}{j+x}=\frac{\Gamma(n+1)\Gamma(x+1)}{\Gamma(n+x+1)}$.

**Theorem.**

1. *(Critical case $\alpha=\tfrac12$.)* With $\mu_n=\delta b_{n,1/2}$ and $\sigma_n^2=\frac1n+(1-\frac1n)\big(\frac{2}{n-1}(H_n-1)-\frac{1}{n-1}\big)-b_{n,1}$,

$$d_K\Big(\mathscr L\big(\tfrac{\overline Y_n-\mu_n}{\sigma_n}\big),N(0,1)\Big)=O\big((\ln n)^{-1}\big),$$

and $(n/\ln n)^{1/2}\,\overline Y_n\Rightarrow N(0,2)$.
2. *(Fast adaptation $\alpha>\tfrac12$.)* With $\mu_n=\delta b_{n,\alpha}$ and

$$\sigma_n^2=\frac1n+\Big(1-\frac1n\Big)\frac{2-(n+1)(2\alpha+1)b_{n,2\alpha}}{(n-1)(2\alpha-1)}-b_{n,2\alpha},$$

the Kolmogorov distance between the standardized average and $N(0,1)$ is

$$O\big(n^{1-2\alpha}\big)\ \ (\tfrac12<\alpha<\tfrac34),\qquad O\big(n^{-1/2}\ln^{1/2}n\big)\ \ (\alpha=\tfrac34),\qquad O\big(n^{-1/2}\big)\ \ (\alpha>\tfrac34),$$

and $\sqrt n\,\overline Y_n\Rightarrow N\big(0,\frac{2\alpha+1}{2\alpha-1}\big)$.
3. *(Wasserstein.)* The same standardized average is within $O((\ln n)^{-1})$ of $N(0,1)$ in $d_W$ for $\alpha=\tfrac12$. For $\alpha>\tfrac12$ the $d_W$ rate is $O(n^{1-2\alpha})$, $O(n^{-1/2}\ln^{1/4}n)$ or $O(n^{-\min(\alpha-1/4,\,3/4)})$ in the three regimes above.

For $\alpha<\tfrac12$, slow adaptation, the bounds give no information, and the limit is expected to be non-normal. These results imply and quantify the earlier central limit theorems of Bartoszek and Sagitov for the YOU model. With normally distributed jumps at speciation (YOUj), analogous rates hold. For example, at $\alpha=\tfrac12$ with constant jump probability and variance, the Kolmogorov rate is $O((\ln n)^{-1/2})$. For $\alpha>\tfrac12$ the source gives rates only for jumps at every speciation with constant variance, $(p_i,\sigma^2_{c,i})\equiv(1,\sigma_c^2)$ (its Theorem 4.1(ii)); under conditions on the jump probabilities $p_n$ and variances $\sigma_{c,n}^2$ such as $p_n\sigma_{c,n}^4\to0$ with density $1$, it proves only convergence of the standardized average to $N(0,1)$, without a rate (its Theorem 4.1(iii)).

## Expansion

Conditionally on the tree, the tip values are jointly Gaussian, so $\overline Y_n$ is a mixture of normals in the sense of the Stein bound in the Depends-on entry. The conditional mean is $\delta$ times an average of $e^{-\alpha T_i}$ over the tip depths $T_i$. The conditional variance is an average over pairs of tips of $e^{-2\alpha\,(\text{time since their common ancestor})}$. Under the Yule tree, depths and coalescence times of random tip pairs have explicit Laplace transforms, which produce the products $b_{n,x}$. The rates follow by computing the leading-order asymptotics of $\mathbb V(\mathbb E(\overline Y_n\mid\mathscr G))$ and $\mathbb V(\mathbb V(\overline Y_n\mid\mathscr G))$ and inserting them into the mixture bounds.

These are the two theorems of Section 3 (YOU) and the two theorems of Section 4 (YOUj) of the source.

## Proof depends on

- [Stein bounds for mixtures of normal distributions](stein-bounds-for-mixtures-of-normal-distributions.md)

## Sources

- K. Bartoszek, T. Erhardsson, "Normal approximation for mixtures of normal distributions and the evolution of phenotypic traits", arXiv:1912.03561 (2019). <https://doi.org/10.48550/arXiv.1912.03561>
- Published version: K. Bartoszek, T. Erhardsson, "Normal approximation for mixtures of normal distributions and the evolution of phenotypic traits", Advances in Applied Probability 53 (2021), 162–188, <https://doi.org/10.1017/apr.2020.53>.
