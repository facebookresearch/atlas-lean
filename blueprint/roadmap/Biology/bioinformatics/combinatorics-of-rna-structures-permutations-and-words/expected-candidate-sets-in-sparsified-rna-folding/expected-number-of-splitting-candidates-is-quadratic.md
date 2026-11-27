# Expected number of splitting candidates is quadratic

**Setting.** In dynamic-programming folding, the optimal score $W_{i,j}$ of the interval $[i,j]$ is computed by the splitting rule $\Lambda^*$, $W_{i,j} = \max_k\{L_{i,k} + L_{k+1,j}\}$, which costs $O(n^3)$ overall. An interval $v$ with optimal solution $L_v$ is a **$\Lambda$-candidate** if $L_v > L_{v_1} + L_{v_2}$ for every proper split $v = v_1 \dot\cup v_2$ produced by $\Lambda$. If the splitting rule is **$s$-compatible** with the enclosing rule, every optimal solution is obtained from candidates only, so the recursion may range over candidates, $W_{i,j} = \max_{[i,k]\ \text{candidate}}\{L_{i,k} + L_{k+1,j}\}$, in time $O(nZ)$ with $Z$ the number of candidates. Under the **polymer-zeta property** (the probability of an unsplittable structure over an interval of length $m$ is $b\,m^{-c}$ with $c > 1$) one gets $\mathbb{E}[Z] = O(n)$ and an $O(n^2)$ algorithm.

Let $\mathbf{d}_g(n)$ count genus-$g$ RNA structures (diagrams over one backbone with $n$ vertices whose fatgraph has topological genus $g$) and $\mathbf{d}^*_g(n)$ the irreducible ones (those that cannot be cut between two vertices without cutting an arc), with generating functions $\mathbf{D}_g$, $\mathbf{D}^*_g$. Let $\Omega(n) = \sum_{m=1}^n(n - m + 1)$ be the number of intervals of a sequence of length $n$.

**Theorem.**

1. (Irreducible structures) $\mathbf{D}_0^* = 1 - 1/\mathbf{D}_0$ and, for $g \ge 1$, $\mathbf{D}^*_g = -\big[(\mathbf{D}^*_0 - 1)\mathbf{D}_g + \sum_{g_1=1}^{g-1}\mathbf{D}^*_{g_1}\mathbf{D}_{g-g_1}\big]/\mathbf{D}_0$. For $g \ge 1$ these are algebraic with $\mathbf{d}^*_g(n) \sim k_g\, n^{3(g - 1/2)}\gamma^n$, $\gamma \approx 2.618$, the same exponential growth and polynomial exponent as $\mathbf{d}_g(n)$.
2. (Fixed-genus structures) If an mfe genus-$g$ structure over an interval of length $m$ is irreducible with probability $\mathbf{d}^*_g(m)/\mathbf{d}_g(m)$, then the expected number of candidates for sequences of length $n$ satisfies

$$\mathbb{E}_g(n) = \Theta(n^2), \qquad \frac{\mathbb{E}_g(n)}{\Omega(n)} \sim \frac{\mathbf{d}^*_g(n)}{\mathbf{d}_g(n)} \sim b_g > 0 .$$

3. (Secondary structures with loop energies) For the energy-weighted generating function $\mathbf{F}_0$ of secondary structures and its irreducible part $\mathbf{F}^*_0$ in a simplified loop-energy model (Boltzmann weights for hairpin, interior and multi-loops), $\mathbf{f}^*_0(n) \sim \alpha n^{-3/2}\gamma^n$ and $\mathbf{f}_0(n) \sim \beta n^{-3/2}\gamma^n$ with $\alpha \approx 0.24$, $\beta \approx 2.88$, $\gamma \approx 2.1673$, and if mfe irreducibility has probability $\mathbf{f}^*_0(m)/\mathbf{f}_0(m)$ then $\mathbb{E}_0(n) = \Theta(n^2)$ with $\mathbb{E}_0(n)/\Omega(n) \to \alpha/\beta \approx 0.08$.

So, unlike the polymer-zeta prediction, the candidate set has quadratic expected size: sparsification of $\Lambda^*$ reduces running time only by a constant factor rather than by a factor of $n$ (a $91\%$ reduction predicted for the simplified loop model, against $96\%$ observed).

## Expansion

Every structure factors uniquely as a sequence of irreducible blocks, so $\mathbf{D}_0 = 1/(1 - \mathbf{D}^*_0)$, and at higher genus the total genus distributes over the blocks, giving the convolution recursion. Since $\mathbf{D}_g$ and $\mathbf{D}^*_g$ have the same dominant singularity and singular exponent, the ratio $\mathbf{d}^*_g(m)/\mathbf{d}_g(m)$ tends to a positive constant rather than decaying like $m^{-c}$. The expected candidate count is $\sum_{m=1}^n (n - m + 1)\,\mathbb{P}_g(m)$; splitting the sum at a fixed $m_0$ and using the limit of $\mathbb{P}_g(m)$ shows it is asymptotic to $b_g\,\Omega(n)$.

## Sources

- Fenix WD Huang, Christian M Reidys, "On the combinatorics of sparsification", Algorithms for Molecular Biology 7 (2012), 28, <https://doi.org/10.1186/1748-7188-7-28>. Published version of arXiv:1201.0308, cited next; locators there refer to the arXiv version.
- Fenix W. D. Huang, Christian M. Reidys, "On the combinatorics of sparsification", arXiv (2011). Definitions 1–3, Lemma 1, Lemma 2, Theorems 1–4, Lemmas 3–4, Background (time reduction figures). <https://doi.org/10.48550/arXiv.1201.0308>
