# Monotone interpretation orderings are compatible with operations

Let $\mathcal A$ be a $\Sigma$-algebra, with nonempty universe, and a well-founded strict partial ordering $\succ$ on its universe, and let $s \succ_{\mathcal A} t$ mean $\mathcal A(\beta)(s) \succ \mathcal A(\beta)(t)$ for every assignment $\beta$. Call $f_{\mathcal A}$ *monotone* if $a \succ a'$ implies $f_{\mathcal A}(b_1, \dots, a, \dots, b_n) \succ f_{\mathcal A}(b_1, \dots, a', \dots, b_n)$. If the interpretation $f_{\mathcal A}$ of every function symbol $f$ is monotone, then $\succ_{\mathcal A}$ is [compatible with $\Sigma$-operations](../reduction-ordering.md): $s \succ_{\mathcal A} s'$ implies $f(t_1, \dots, s, \dots, t_n) \succ_{\mathcal A} f(t_1, \dots, s', \dots, t_n)$ for every function symbol $f$ and all terms $t_i$.

**Proof.** For every assignment $\beta$, $\mathcal A(\beta)(f(t_1, \dots, s, \dots, t_n)) = f_{\mathcal A}(\dots, \mathcal A(\beta)(s), \dots) \succ f_{\mathcal A}(\dots, \mathcal A(\beta)(s'), \dots)$ by monotonicity. Well-foundedness is not used; the source assumes it throughout the interpretation method, where $\succ_{\mathcal A}$ is to be a reduction ordering.

## Depends on

- [Reduction ordering](../reduction-ordering.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, the setup of the interpretation method (a well-founded strict partial ordering on the universe), Lemma 4.21 and its proof, pp. 115–116.
