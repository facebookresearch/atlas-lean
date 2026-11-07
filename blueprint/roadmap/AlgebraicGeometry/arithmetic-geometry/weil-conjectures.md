# The Weil conjectures

Let $F$ be a finite field with $q$ elements, and let $X$ be a scheme
over $\operatorname{Spec} F$ whose structure morphism is proper, geometrically irreducible and
smooth of relative dimension $d$. Then there is a sequence $A_0, A_1, A_2, \dots$ of finite
multisets of complex numbers with $A_0 = \{1\}$ such that, for every $0 \le i \le 2d$, the
multiset $A_{2d-i}$ is the image of $A_i$ under $\alpha \mapsto q^d/\alpha$, the multiset $A_i$
is invariant under every field automorphism of $\mathbb{C}$, and every $\alpha \in A_i$ is an
algebraic integer with $|\alpha| = \sqrt{q^i}$. Moreover, for every finite field extension $E$
of $F$ of degree $m$, the number of morphisms $\operatorname{Spec} E \to X$ over
$\operatorname{Spec} F$ equals $\sum_{i=0}^{2d} (-1)^i \sum_{\alpha \in A_i} \alpha^m$, where
the inner sums count multiplicities.

## Sources

- P. Deligne, 'La conjecture de Weil. I', Publications Mathématiques de l'Institut des Hautes Études Scientifiques, Volume 43, pages 273–307 (1974), https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf. See also references in the Lean file. Via leanprover/lean-eval@38361be, problem `weil_conjectures`.
