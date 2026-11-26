# The integral expectation threshold of an increasing family

Let $\mathcal{F}$ be a nontrivial increasing family of subsets of a finite set $X$, with threshold $p_c(\mathcal{F})$ and largest minimal-element size $\ell(\mathcal{F})$. A family $\mathcal{G} \subseteq 2^X$ **covers** $\mathcal{F}$ if every member of $\mathcal{F}$ contains a member of $\mathcal{G}$. The **(integral) expectation threshold** is

$$
q(\mathcal{F}) = \max\Bigl\{\, p \;:\; \exists\, \mathcal{G} \text{ covering } \mathcal{F} \text{ with } \sum_{S \in \mathcal{G}} p^{|S|} \le \tfrac{1}{2} \,\Bigr\}.
$$

By the first-moment method $q(\mathcal{F}) \le p_c(\mathcal{F})$, and since an integral cover is a fractional one, $q(\mathcal{F}) \le q_f(\mathcal{F})$, where $q_f$ is the fractional expectation threshold.

## Depends on

- [The threshold $p_c(\mathcal F)$](../../probabilistic-combinatorics/thresholds-and-expectation-thresholds/p-c.md)
- [Size of a largest minimal element, $\ell(\mathcal F)$](../../probabilistic-combinatorics/thresholds-and-expectation-thresholds/l.md)
- [The fractional expectation-threshold $q_f(\mathcal F)$](../../probabilistic-combinatorics/thresholds-and-expectation-thresholds/q-f.md)

## Sources

- J. Kahn, G. Kalai, "Thresholds and expectation thresholds", Combinatorics, Probability and Computing 16 (2007) 495-502.
- J. Park, H. T. Pham, "A proof of the Kahn-Kalai conjecture", Journal of the American Mathematical Society 37 (2024) 235-243, arXiv:2203.17207.
