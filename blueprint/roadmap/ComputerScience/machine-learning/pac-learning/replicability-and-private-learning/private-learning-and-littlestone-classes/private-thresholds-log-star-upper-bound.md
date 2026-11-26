# Private learning of thresholds with nearly log-star sample complexity

Let $X$ be a finite totally ordered domain and $H$ the thresholds $\{x \mapsto \mathbf{1}[x \ge a] : a \in X\}$. There is an approximately differentially private PAC learner for $H$ with sample complexity $\tilde O(\log^* |X|)$, as a function of $|X|$ for constant privacy and accuracy parameters, matching the $\Omega(\log^* |X|)$ lower bound. Moreover, private quasi-concave optimization over $X$ has optimal additive error $\tilde\Theta(2^{\log^* |X|})$. Earlier constructions achieved $2^{O(\log^* |X|)}$ and then $\tilde O((\log^* |X|)^{1.5})$ samples.

## Proof sketch

The Reorder-Slice-Compute paradigm repeatedly reorders the domain according to a privately computed ranking of candidate thresholds, restricts attention to a slice whose size is logarithmic in the previous domain, and recurses; each level costs only an additive $\tilde O(1)$ samples because the privacy loss is charged to the small slice rather than to the full domain, and there are $\log^* |X|$ levels. The quasi-concave optimization bounds follow from the same recursion and a matching packing construction.

## Depends on

- [Private PAC learners and their sample complexity](private-pac-learner.md)

## Proof depends on

- [Private learning requires log-star of the Littlestone dimension samples](private-learning-requires-log-star-littlestone.md)

## Sources

- E. Cohen, X. Lyu, J. Nelson, T. Sarlos, U. Stemmer, "Optimal Differentially Private Learning of Thresholds and Quasi-Concave Optimization", STOC (2023), arXiv:2211.06387.
- H. Kaplan, K. Ligett, Y. Mansour, M. Naor, U. Stemmer, "Privately Learning Thresholds: Closing the Exponential Gap", COLT (2020), arXiv:1911.10137.
