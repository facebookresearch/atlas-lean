# Interpretation orderings are stable under substitutions

Let $\mathcal A$ be a $\Sigma$-algebra, with nonempty universe, and a well-founded strict partial ordering $\succ$ on its universe $U_{\mathcal A}$, and for terms $s, t \in T_\Sigma(X)$ let $s \succ_{\mathcal A} t$ mean $\mathcal A(\beta)(s) \succ \mathcal A(\beta)(t)$ for every assignment $\beta : X \to U_{\mathcal A}$. Then $\succ_{\mathcal A}$ is [stable under substitutions](../reduction-ordering.md): if $s \succ_{\mathcal A} t$, then $s\sigma \succ_{\mathcal A} t\sigma$ for every substitution $\sigma$.

**Proof.** For an assignment $\gamma$, let $\beta = \gamma \circ \sigma$ be the assignment $\beta(x) = \mathcal A(\gamma)(\sigma(x))$. Then $\mathcal A(\gamma)(u\sigma) = \mathcal A(\beta)(u)$ for every term $u$, by induction on $u$: for a variable $x$ both sides are $\mathcal A(\gamma)(\sigma(x))$, and for $u = f(u_1, \dots, u_n)$ both sides apply $f_{\mathcal A}$ to equal arguments. Hence $\mathcal A(\gamma)(s\sigma) = \mathcal A(\beta)(s) \succ \mathcal A(\beta)(t) = \mathcal A(\gamma)(t\sigma)$.

## Depends on

- [Reduction ordering](../reduction-ordering.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, Lemma 4.20 and its proof, p. 115; Section 3.3, Lemma 3.4 (the substitution lemma, with $\beta \circ \sigma(x) = \mathcal A(\beta)(x\sigma)$), p. 53.
