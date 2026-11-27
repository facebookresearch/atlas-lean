# Entropy of decidable f-irreducible subshifts is not computable when the sum of f(n)/n² diverges

If a nondecreasing function $f$ has $\sum_n f(n)/n^2 = +\infty$, the entropies of decidable $f$-irreducible subshifts are exactly the nonnegative $\Pi_1$-computable reals, and no algorithm computes the entropy of these subshifts.

Let $d \ge 1$ and let $\Sigma \subseteq \mathcal{A}^{\mathbb{Z}^d}$ be a subshift over a finite alphabet, with language $\mathcal{L}(\Sigma)$ (the finite patterns that appear in some configuration) and $\mathcal{L}_n(\Sigma)$ its patterns on the cube $\{0, \dots, n-1\}^d$. Its *entropy* is

$$
h(\Sigma) = \lim_{n \to \infty} \frac{\log_2 \#\mathcal{L}_n(\Sigma)}{n^d} .
$$

- $\Sigma$ is *decidable* if $\mathcal{L}(\Sigma)$ is a decidable set of patterns; a decidable subshift is given to an algorithm by a decision procedure for its language.
- For $f\colon \mathbb{N} \to \mathbb{N}$, $\Sigma$ is *$f$-irreducible* if for all finite $\mathbb{U}, \mathbb{V} \subset \mathbb{Z}^d$ with $d(\mathbb{U}, \mathbb{V}) \ge f(\max(\delta(\mathbb{U}), \delta(\mathbb{V})))$, where $d$ is the sup-distance between the sets and $\delta$ the sup-diameter, and all $u \in \mathcal{L}_{\mathbb{U}}(\Sigma)$, $v \in \mathcal{L}_{\mathbb{V}}(\Sigma)$, there is $x \in \Sigma$ with $x_{\mathbb{U}} = u$ and $x_{\mathbb{V}} = v$.
- A real $\alpha$ is *$\Pi_1$-computable* (upper semi-computable) if $\alpha = \inf_n \varphi(n)$ for a computable $\varphi\colon \mathbb{N} \to \mathbb{Q}$, and *computable* if some computable $\varphi$ has $|\alpha - \varphi(n)| \le 2^{-n}$ for all $n$.

**Theorem.** Let $f\colon \mathbb{N} \to \mathbb{N}$ be nondecreasing with

$$
\sum_{n=1}^{\infty} \frac{f(n)}{n^2} = +\infty .
$$

Then the set of entropies of decidable $f$-irreducible subshifts is exactly the set of $\Pi_1$-computable numbers, and there is no algorithm that computes the entropy of these subshifts (Main Theorem, item 2, of the source); the source states that this applies to one-dimensional and multidimensional decidable subshifts. If moreover $f$ is computable, then for every $\Pi_1$-computable real $\alpha > 0$ there is a decidable $f$-irreducible one-dimensional subshift with entropy $\alpha$ (Theorem 3.7).

## Depends on

- [Subshifts of finite type on a finitely generated group and the domino problem](subshifts-of-finite-type-on-groups.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The entropy of a decidable subshift is always $\Pi_1$-computable, since $h(\Sigma) = \inf_n \log_2 \#\mathcal{L}_n(\Sigma)/n^d$ and each term is computable from the decision procedure. For the converse the source uses bounded density subshifts (subshifts of $\{0, 1\}^{\mathbb{Z}}$ in which every word of length $n$ has at most $p_n$ symbols $1$, for a sequence $p$), with density bounds built from $f$ and from a computable sequence of upper approximations of $\alpha$; decidability, $f$-irreducibility and entropy $\alpha$ are then checked for this subshift, and the result is extended to every $d \ge 2$. Since there are $\Pi_1$-computable reals that are not computable, for instance $\sum_k \varepsilon_k 2^{-k}$ with $\varepsilon_k = 0$ exactly when the $k$-th Turing machine halts on the empty input, no algorithm computes the entropy of all decidable $f$-irreducible subshifts. The threshold is sharp: if $\sum f(n)/n^2$ converges at a computable rate, an algorithm computes the entropy of $f$-irreducible decidable subshifts (Theorems 3.5 and 3.6 of the source), for example for $f(n) = n/(\log_2 n)^{1+\varepsilon}$.

## Sources

- S. Gangloff and B. Hellouin de Menibus, "Effect of quantified irreducibility on the computability of subshift entropy", Discrete and Continuous Dynamical Systems 39 (2019), no. 4, 1975–2000, https://doi.org/10.3934/dcds.2019083; read in arXiv:1602.06166v3 (the Main Theorem in the introduction, Definition 2.1 and the definitions of computable and $\Pi_1$-computable reals and decidable subshifts in Section 2, and Theorems 3.5, 3.6 and 3.7 of arXiv:1602.06166v3).
