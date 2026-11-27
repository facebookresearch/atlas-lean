# Private learning of thresholds with nearly log-star sample complexity

Let $X$ be a finite totally ordered domain and $H$ the thresholds $\{x \mapsto \mathbf{1}[x \ge a] : a \in X\}$. For all $\varepsilon, \delta, \xi, \beta \in (0,1)$ there is an $(\varepsilon,\delta)$-differentially private PAC learner for $H$ with error $\xi$ and confidence $1-\beta$ using $O\big(\log^* |X| \cdot \log^2(\log^* |X|/(\beta\delta))/(\xi\varepsilon)\big)$ samples, which is $\tilde O(\log^* |X|)$ as a function of $|X|$ for constant $\varepsilon, \xi, \beta$ and $\delta = O(1/(n^2\log n))$. In that regime it matches the $\Omega(\log^* |X|)$ lower bound of Alon, Livni, Malliaris and Moran, which is proved for $\varepsilon = 0.1$ and $\delta = O(1/(n^2 \log n))$ and needs $\delta$ that small: for a fixed constant $\delta$, privacy can be obtained by subsampling at a sample size independent of $|X|$ (running a non-private learner on a uniformly random $m$ of the $n$ examples is $(0, m/n)$-differentially private, so $n = m/\delta$ samples suffice), and no $\log^* |X|$ lower bound holds. Moreover, private quasi-concave optimization over $X$ has optimal additive error $\tilde\Theta(2^{\log^* |X|})$. Earlier constructions achieved $2^{O(\log^* |X|)}$ and then $\tilde O((\log^* |X|)^{1.5})$ samples.

## Proof sketch

The Reorder-Slice-Compute paradigm repeatedly reorders the domain according to a privately computed ranking of candidate thresholds, restricts attention to a slice whose size is logarithmic in the previous domain, and recurses; each level costs only an additive $\tilde O(1)$ samples because the privacy loss is charged to the small slice rather than to the full domain, and there are $\log^* |X|$ levels. The quasi-concave optimization bounds follow from the same recursion and a matching packing construction.

## Depends on

- [Private PAC learners and their sample complexity](private-pac-learner.md)

## Proof depends on

- [Private learning requires log-star of the Littlestone dimension samples](private-learning-requires-log-star-littlestone.md)

## Sources

- E. Cohen, X. Lyu, J. Nelson, T. Sarlos, U. Stemmer, "Optimal Differentially Private Learning of Thresholds and Quasi-Concave Optimization", STOC (2023), arXiv:2211.06387, Theorems 1.2, 3.9, 4.2 and 4.4.
- H. Kaplan, K. Ligett, Y. Mansour, M. Naor, U. Stemmer, "Privately Learning Thresholds: Closing the Exponential Gap", COLT (2020), arXiv:1911.10137.
