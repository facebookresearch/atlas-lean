# Monotone interpretation orderings are compatible with operations

Let $\mathcal A$ be a $\Sigma$-algebra with a strict partial ordering $\succ$ on its universe, and let $s \succ_{\mathcal A} t$ mean $\mathcal A(\beta)(s) \succ \mathcal A(\beta)(t)$ for every assignment $\beta$. Call $f_{\mathcal A}$ *monotone* if $a \succ a'$ implies $f_{\mathcal A}(b_1, \dots, a, \dots, b_n) \succ f_{\mathcal A}(b_1, \dots, a', \dots, b_n)$. If the interpretation $f_{\mathcal A}$ of every function symbol $f$ is monotone, then $s \succ_{\mathcal A} s'$ implies $f(t_1, \dots, s, \dots, t_n) \succ_{\mathcal A} f(t_1, \dots, s', \dots, t_n)$ for every function symbol $f$ and all terms $t_i$.

**Proof.** For every assignment $\beta$, $\mathcal A(\beta)(f(t_1, \dots, s, \dots, t_n)) = f_{\mathcal A}(\dots, \mathcal A(\beta)(s), \dots) \succ f_{\mathcal A}(\dots, \mathcal A(\beta)(s'), \dots)$ by monotonicity.

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, Lemma 4.21 and its proof, pp. 115–116.
