# Interpretation orderings are stable under substitutions

Let $\mathcal A$ be a $\Sigma$-algebra with a well-founded strict partial ordering $\succ$ on its universe $U_{\mathcal A}$, and for terms $s, t \in T_\Sigma(X)$ let $s \succ_{\mathcal A} t$ mean $\mathcal A(\beta)(s) \succ \mathcal A(\beta)(t)$ for every assignment $\beta : X \to U_{\mathcal A}$. If $s \succ_{\mathcal A} t$, then $s\sigma \succ_{\mathcal A} t\sigma$ for every substitution $\sigma$.

**Proof.** For an assignment $\gamma$, take $\beta = \gamma \circ \sigma$; by the substitution lemma, $\mathcal A(\gamma)(s\sigma) = \mathcal A(\beta)(s) \succ \mathcal A(\beta)(t) = \mathcal A(\gamma)(t\sigma)$.

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, Lemma 4.20 and its proof, p. 115.
