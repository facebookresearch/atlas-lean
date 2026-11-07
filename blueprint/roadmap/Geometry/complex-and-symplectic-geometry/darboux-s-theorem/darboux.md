# Darboux's theorem

Let $n$ be a natural number, let $U$ be an open subset of the model
space $\mathbb{R}^{2n}$, and let $\alpha$ be a field of continuous alternating 2-forms on
$\mathbb{R}^{2n}$ that is symplectic on $U$. Then for every $x \in U$ there is an open partial
homeomorphism $\varphi$ of $\mathbb{R}^{2n}$ whose source contains $x$ and is contained in $U$, such
that $\varphi$ is $C^\infty$ on its source, $\varphi^{-1}$ is $C^\infty$ on its target, and for
every $z$ in the target the pullback of $\alpha(\varphi^{-1}(z))$ by the derivative
$D\varphi^{-1}(z)$, namely
$(v, w) \mapsto \alpha(\varphi^{-1}(z))(D\varphi^{-1}(z)\, v, D\varphi^{-1}(z)\, w)$, is in Darboux
normal form.

## Sources

- J. G. Darboux, Sur le problème de Pfaff, Bull. Sci. Math. 6 (1882), 14-36, 49-68. Listed as §39 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `darboux`.
