# Mode of the k-mismatch extension length distribution

**Model.** Two DNA sequences $S_1, S_2$ of equal length $L$ evolve without indels from a common
ancestor. Aligned (homologous) positions match with probability $p$, and unaligned (background) pairs
match with probability $q$, all position pairs independently:
$P(S_1(i) = S_2(j)) = p$ if $i = j$ and $q$ otherwise. The target is $p$, from which the number of
substitutions per site follows by the Jukes-Cantor correction.

**k-mismatch extensions.** For position $i$ of $S_1$ let $X_i$ be the length of the longest substring
starting at $i$ that occurs exactly in $S_2$, starting at $j^*$. Skip the mismatch that ends this match
and let $\hat{X}_i(k)$ be the length of the longest gap-free extension starting at $i + X_i + 1$ in
$S_1$ and $j^* + X_i + 1$ in $S_2$ with Hamming distance exactly $k$ (it ends just before the
$(k+1)$-st mismatch).

**Theorem.** Ignore edge effects (the sequences are long enough that no extension reaches their ends) and assume $j^* \ne i$ whenever the longest exact match starting at $i$ also occurs at a position other than $i$ (ties are resolved against the homologous position). Then for $m \ge k$,

$$P\bigl(\hat{X}_i(k) = m\bigr) = P(j^* = i) \binom{m}{k} p^{m-k} (1-p)^{k+1} + P(j^* \ne i) \binom{m}{k} q^{m-k} (1-q)^{k+1},$$

a mixture of a homologous and a background negative binomial law, each unimodal. The homologous part
$H_k(m)$ satisfies $H_k(m+1) = \frac{(m+1)p}{m+1-k} H_k(m)$, so it increases exactly while
$\frac{m+1-k}{m+1} \le p$, with maximum near $m_H = \frac{k}{1-p} - 1$; the background part peaks near
$m_B = \frac{k}{1-q} - 1$. Moreover $P(j^* = i) = \sum_m (1 - q^m)^{L-1} p^m (1-p)$.

**Estimator.** If $m_{\max}$ is the mode of the homologous part,
$\frac{m_{\max} - k}{m_{\max}} \le p \le \frac{m_{\max} + 1 - k}{m_{\max} + 1}$, so the second peak $m_E$ of the
smoothed empirical length distribution gives

$$\hat{p} \approx \frac{m_E + 1 - k}{m_E + 1}.$$

## Depends on

- [Jukes–Cantor distance](../../jukes-cantor-model/jc-distance.md)

## Expansion

Conditional on the exact match being homologous ($j^* = i$), positions after it are independent
Bernoulli($p$) matches, so the extension length is the number of trials before the $(k+1)$-st failure,
a negative binomial; the background case is identical with $q$. For realistic genome lengths
$P(j^* = i) \ll P(j^* \ne i)$, so moment estimators built on the average match length are swamped by
background matches. Because $p > q$, choosing $k$ large separates $m_H$ from $m_B$, and the location of
the homologous peak, unlike its height, does not depend on the unknown mixing weight. The estimate is
then insensitive to the background fraction and works on real sequences with indels.

## Sources

- B. Morgenstern, S. Schöbel, C.-A. Leimeister, "Phylogeny reconstruction based on the length
  distribution of k-mismatch common substrings", Algorithms for Molecular Biology 12 (2017),
  Theorem 2 and Eqs. 16-19, <https://doi.org/10.1186/s13015-017-0118-8> (PMC5724348).
