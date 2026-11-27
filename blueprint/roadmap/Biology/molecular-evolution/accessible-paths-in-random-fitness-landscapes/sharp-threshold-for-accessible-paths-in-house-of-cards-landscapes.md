# Sharp threshold for accessible paths in house-of-cards landscapes

**Setting.** Genotypes are the vertices of the hypercube $\mathbb{Q}_n = \{0,1\}^n$; a mutation flips one bit. A path from $\mathbf{v}^0 = 0^n$ to $\mathbf{v}^1 = 1^n$ of length $n$ (each bit flipped once) is **accessible** if fitness strictly increases along it. Models:
- *House of cards (HoC):* $f(\mathbf v^1) := 1$, and all other fitnesses ($f(\mathbf v^0)$ included) are i.i.d. $\mathrm{Uniform}[0,1]$.
- *$\alpha$-HoC:* as HoC, except $f(\mathbf v^0) := \alpha \in [0,1]$.
- *Rough Mount Fuji (RMF):* $f(v) = \theta_n\, d(v,\mathbf{v}^0) + \eta(v)$, with $d$ the Hamming distance, drift $\theta_n > 0$ and i.i.d. noise $\eta(v)$.

Let $P(n,\alpha)$ be the probability that the $\alpha$-HoC landscape has at least one accessible path, and $X$ the number of accessible paths.

**Theorem.**
1. (Sharp threshold) If $n\varepsilon_n \to \infty$, then $P\big(n, \tfrac{\ln n}{n} - \varepsilon_n\big) \to 1$ and $P\big(n, \tfrac{\ln n}{n} + \varepsilon_n\big) \to 0$. In particular CHoC has an accessible path with probability tending to $1$.
2. (HoC) In the unconstrained house-of-cards model, $\mathbb{P}(X > 0) \sim \frac{\ln n}{n} \to 0$.
3. (Concentration) In $\alpha$-HoC with $\alpha = \frac{\ln n}{n} - \varepsilon_n$, $n\varepsilon_n\to\infty$, for any $w_n \to \infty$, $\mathbb{P}\big(\mathbb{E}[X]/w_n \le X \le w_n\mathbb{E}[X]\big) \to 1$, where $\mathbb{E}[X] = n(1-\alpha)^{n-1}$.
4. (RMF) If $\eta$ has a density continuous on its connected support and $n\theta_n \to \infty$, then the RMF landscape has an accessible path from $\mathbf{v}^0$ to $\mathbf{v}^1$ with probability tending to $1$.

## Depends on

- [Accessible mutational paths in the House-of-Cards landscape](../../population-genetics/selection-migration-and-transmission/fitness-landscapes/accessible-adaptive-paths.md)

## Proof depends on

## Expansion

Each of the $n!$ paths has interior fitnesses i.i.d. uniform, so it is accessible in $\alpha$-HoC with probability $(1-\alpha)^{n-1}/(n-1)!$, giving $\mathbb{E}[X] = n(1-\alpha)^{n-1}$, which crosses order $1$ at $\alpha = \ln n / n$. The first-moment method gives the upper half of the threshold. For the lower half, a second-moment computation (Proposition 2.15) shows $\mathbb{E}[X^2] \sim 4n^2(1-\alpha)^{2n}$, within a constant factor of $\mathbb{E}[X]^2$, controlled by counting pairs of paths by their shared interior vertices through the numbers $T(n,k)$ of permutations decomposing into $k$ indecomposable blocks; this second-moment control is then refined into the probability-one statement. In plain HoC the starting fitness is uniform, and the threshold result integrated over $f(\mathbf{v}^0)$ gives probability about $\ln n / n$. In RMF, any drift with $n\theta_n\to\infty$ eventually dominates the noise along enough paths.

## Sources

- Peter Hegarty and Anders Martinsson, "On the existence of accessible paths in various models of fitness landscapes", arXiv:1210.4798 (2012), Section 1 (Definition 1.1 and the models), Theorem 1.2, Corollaries 1.3 and 1.4, Theorem 1.5, Propositions 2.1 and 2.15; published in *Annals of Applied Probability* 24(4) (2014) 1375–1395, <https://doi.org/10.1214/13-AAP949>.
