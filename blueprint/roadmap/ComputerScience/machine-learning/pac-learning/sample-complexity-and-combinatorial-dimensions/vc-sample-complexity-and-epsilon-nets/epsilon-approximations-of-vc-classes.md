# Existence of epsilon-approximations for classes of finite VC dimension

Let $Z$ be a countable set with all subsets measurable and let $G$ be a class of functions $Z \to \{0,1\}$ such that every finite set shattered by $G$ has at most $d$ points.
For a probability measure $\mu$ on $Z$ and $\varepsilon > 0$, a sequence $S \in Z^m$ is an $\varepsilon$-approximation for $G$ under $\mu$ if $\big|\tfrac{1}{m}\#\{i : g(S_i) = 1\} - \mu(g = 1)\big| < \varepsilon$ for every $g \in G$. For every $\varepsilon, \delta \in (0,1)$ and every

$$
m \ge \frac{16}{\varepsilon^2}\Big(2d \ln\frac{10}{\varepsilon} + \ln\frac{4}{\delta}\Big),
$$

$m$ i.i.d. samples from $\mu$ form an $\varepsilon$-approximation with probability at least $1 - \delta$; in particular every probability measure on $Z$ (including one given by a probability mass function on a countable set) has an $\varepsilon$-approximation of that size, independent of $\mu$.

## Proof sketch

This is the Vapnik-Chervonenkis inequality with Sauer's lemma: the failure probability is below $\delta < 1$, so some sample succeeds.

## Depends on

- [The VC dimension is at most the size of the ground set](../../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md)

## Proof depends on

- [Vapnik-Chervonenkis inequality: uniform convergence from the growth function](vapnik-chervonenkis-inequality.md)

## Sources

- V. N. Vapnik and A. Ya. Chervonenkis, "On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities", Theory of Probability and Its Applications, 1971.
- S. Moran and A. Yehudayoff, "Sample Compression Schemes for VC Classes", Journal of the ACM, 2016.
