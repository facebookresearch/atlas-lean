# Stationary extrema are local minima of expected-step divergences

**Incentive process.** A population of fixed size $N$ consists of $a_i$ individuals of type $A_i$, $i = 1,\dots,n$; write $\bar a = a/N$. An *incentive* $\varphi(\bar a) = (\varphi_1(\bar a), \dots, \varphi_n(\bar a))$, positive at interior states (e.g. the replicator incentive $\varphi_i = \bar a_i f_i(\bar a)$ for a fitness landscape $f$), and a mutation matrix $M$ define the reproduction probabilities

$$ p_i(\bar a) = \frac{\sum_k \varphi_k(\bar a) M_{ki}}{\sum_k \varphi_k(\bar a)}. $$

In each step an individual reproduces with type distribution $p(\bar a)$ and a uniformly chosen individual dies, so $T_a^{a + i_{\alpha\beta}} = p_\alpha(\bar a)\,\bar a_\beta$ for $\alpha \ne \beta$, where $i_{\alpha\beta}$ adds one $A_\alpha$ and removes one $A_\beta$. The Wright–Fisher variant samples the next generation multinomially from $p(\bar a)$. Let $s$ be the stationary distribution, $E(\bar a)$ the expected distribution after one step, and for $0 \le d \le 1$

$$ \hat D_d(x, y) = \frac{1}{1-d}\sum_i\Big[\frac{x_i^{2-d} - y_i^{2-d}}{2-d} - y_i^{1-d}(x_i - y_i)\Big] \quad (0 < d < 1), $$

with $\hat D_0(x,y) = \frac12\|x-y\|^2$ and $\hat D_1(x,y) = \sum_i x_i\log(x_i/y_i)$ the relative entropy; put $D_d(a) = \hat D_d(E(\bar a), \bar a)$. A state is an *ISS candidate* if $\bar a = p(\bar a)$, and *stationary stable* if $s$ has a local maximum there.

**Proposition.** For the incentive process and the Wright–Fisher process the following are equivalent: $\bar a = p(\bar a)$; $E(\bar a) = \bar a$; $D_d(a) = 0$ for all $0 \le d \le 1$. For the incentive process $E(\bar a) = \frac{N-1}{N}\bar a + \frac1N p(\bar a)$.

**Theorem.**

1. *(Two types.)* For a continuous incentive and mutation matrix there is $N_0$ such that for $N > N_0$ every local maximum or minimum of the stationary distribution of the incentive process is a local minimum of $D_d$ for $0 \le d < 1$, and interior extrema are local minima of the relative entropy $D_1$. The same holds for the $k$-fold process (the $k$-th power of the transition matrix).
2. *($n$ types.)* For a continuous incentive and mutation matrix and $N$ large enough, states that are *probability-flow neutral* (inflow and outflow of stationary probability approximately balance, which holds at extrema of $s$ for large $N$) are local minima of $D_d$ for $0 \le d < 1$, and interior ones of $D_1$.
3. *(Wright–Fisher.)* If the stationary distribution of the Wright–Fisher process has a global maximum at $a$, is symmetric about it and is otherwise vanishingly small, then for large $N$, $a$ is an ISS candidate and a minimum of $D_d$.

For two types, linear landscapes and the Moran process with $\mu \to 0$ as $N \to \infty$, there is asymptotically at most one interior stationary stable state; in the large-population limit the replicator-equation stability theory, with the relative entropy as Lyapunov function, is recovered.

## Expansion

For two types the chain is tridiagonal and reversible, so $s_{i+1}/s_i = T_i^{i+1}/T_{i+1}^{i}$, and as $N \to \infty$ consecutive transition probabilities differ by $o(1)$ (continuity of the incentive). At an extremum of $s$ the ratio is close to $1$ on both sides, hence $T_i^{i+1} \approx T_i^{i-1}$, which by $E(\bar a) = \bar a + \frac1N(T_i^{i+1} - T_i^{i-1})(1,-1)$ makes $E(\bar a) \approx \bar a$ and the divergences nearly zero; positive definiteness of $\hat D_d$ then gives local minimality. With more types detailed balance fails in general, and the global balance equations $s_a\sum_b T_a^b = \sum_b s_b T_b^a$ replace it, which yields the probability-flow-neutral condition. Powers of a transition matrix preserve the stationary distribution and detailed balance, which transfers the results to $k$-fold processes. Because $\hat D_d$ is dominated by the $\chi^2$-divergence, small expected displacement controls all members of the family at once.

## Sources

- Marc Harper, Dashiell Fryer, "Stationary stability for evolutionary dynamics in finite populations", arXiv:1311.0941 (2013), Section 2 (incentive process, Wright–Fisher process, stationary distributions), Section 3 (distance functions, Propositions 1–3), Section 4 (Lemma 1, Theorem 1, Corollary 4, Propositions 5–6, Corollary 7), Section 5 (Proposition 8, Theorems 2–3), Section 6 (Theorem 4). <https://doi.org/10.48550/arXiv.1311.0941>. Published version: Entropy 18(9) (2016), article 316, <https://doi.org/10.3390/e18090316>; locators above refer to the arXiv version.
