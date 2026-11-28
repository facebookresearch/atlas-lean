# Private learning of thresholds with nearly log-star sample complexity

Let $X$ be a finite totally ordered domain and $H$ the thresholds $\{x \mapsto \mathbf{1}[x \ge a] : a \in X\}$. For all $\varepsilon, \delta, \xi, \beta \in (0,1)$ there is a sample size

$$
n \le O\Big(\frac{\log^* |X| \cdot \log^2\big(\log^* |X|/(\beta\delta)\big)}{\xi\varepsilon}\Big)
$$

and an $(\varepsilon,\delta)$-differentially private learner on $n$ examples that, in the realizable setting, outputs a threshold with error at most $\xi$ with probability at least $1-\beta$ (Theorem 3.9). The dependence on $\delta$ is kept: an upper bound such as $\delta = O(1/(n^2 \log n))$ alone allows $\delta = e^{-|X|}$, for which the bound is not $\tilde O(\log^* |X|)$. For constant $\varepsilon, \xi, \beta$ and $\log(1/\delta) = O(\log \log^* |X|)$ the sample size is $O(\log^* |X| \cdot \log^2 \log^* |X|) = \tilde O(\log^* |X|)$. In particular, in the two-sided regime $\delta = \Theta(1/(n^2 \log n))$, where $n$ is the learner's own sample size, there are learners on $n = O(\log^* |X| \cdot \log^2 \log^* |X|)$ examples, which matches up to lower-order terms the $\Omega(\log^* |X|)$ lower bound of Alon, Livni, Malliaris and Moran, proved for $\varepsilon = 0.1$ and $\delta = O(1/(n^2 \log n))$. That lower bound needs $\delta$ that small: for a fixed constant $\delta$, privacy can be obtained by subsampling at a sample size independent of $|X|$ (running a non-private learner on a uniformly random $m$ of the $n$ examples is $(0, m/n)$-differentially private, so $n = m/\delta$ samples suffice), and no $\log^* |X|$ lower bound holds.

For private quasi-concave optimization over $X$, with a quasi-concave score function of sensitivity one (changing one data point changes every score by at most $1$): for all $\varepsilon, \delta \in (0,1)$ there is an $(\varepsilon,\delta)$-differentially private algorithm with additive error $O\big(2^{\log^* |X|} \log^* |X| (\log^* |X| + \log(1/\delta))/\varepsilon\big)$, which is $\tilde O(2^{\log^* |X|}/\varepsilon)$ for constant $\delta$ (Theorem 4.2 and its corollary); and for $\varepsilon = 0.2$ and $\delta = 1/50$, hence also for all smaller $\varepsilon$ and $\delta$, every $(\varepsilon,\delta)$-differentially private algorithm has additive error at least $2^{\log^* |X| - O(\log^* \log^* |X|)}$ on all sufficiently large domains (Theorem 4.4 and its corollary). So for constant $\varepsilon \le 0.2$ and $\delta \le 1/50$ the optimal additive error is $\tilde\Theta(2^{\log^* |X|})$. Earlier threshold learners used $2^{O(\log^* |X|)}$ and then $\tilde O((\log^* |X|)^{1.5})$ samples.

## Proof sketch

The Reorder-Slice-Compute paradigm repeatedly reorders the domain according to a privately computed ranking of candidate thresholds, restricts attention to a slice whose size is logarithmic in the previous domain, and recurses; each level costs only an additive $\tilde O(1)$ samples because the privacy loss is charged to the small slice rather than to the full domain, and there are $\log^* |X|$ levels. The quasi-concave optimization bounds follow from the same recursion and a matching packing construction. For the two-sided regime, take $\delta_0 = 1/(n_0^2 \log n_0)$ for $n_0 = C \log^* |X| \cdot \log^2 \log^* |X|$ with $C$ large: then $\log(1/\delta_0) = O(\log \log^* |X|)$, so Theorem 3.9 gives a learner on at most $n_0$ examples, and padding it to exactly $n_0$ examples (ignoring the extra ones) keeps it $(\varepsilon, \delta_0)$-differentially private.

## Depends on

- [Private PAC learners and their sample complexity](private-pac-learner.md)

## Proof depends on

- [Private learning requires log-star of the Littlestone dimension samples](private-learning-requires-log-star-littlestone.md)

## Sources

- E. Cohen, X. Lyu, J. Nelson, T. Sarlos, U. Stemmer, "Optimal Differentially Private Learning of Thresholds and Quasi-Concave Optimization", STOC (2023), arXiv:2211.06387, Theorems 1.2, 3.9, 4.2 and 4.4.
- H. Kaplan, K. Ligett, Y. Mansour, M. Naor, U. Stemmer, "Privately Learning Thresholds: Closing the Exponential Gap", COLT (2020), arXiv:1911.10137.
