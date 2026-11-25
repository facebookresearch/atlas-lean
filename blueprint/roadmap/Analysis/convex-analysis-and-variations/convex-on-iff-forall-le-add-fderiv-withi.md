# Convexity via the tangent-plane inequality

Let $E$ be a real Banach space, let
$X \subseteq E$ be an open convex set, and let $f \colon E \to \mathbb{R}$ be twice continuously
differentiable on $X$. Then $f$ is convex on $X$ if and only if
$f(x) \ge f(a) + Df(a)(x - a)$ for all $a, x \in X$, where $Df(a)$ is the Fréchet derivative of
$f$ at $a$ within $X$.

Only differentiability on $X$ is used: the statement is a corollary of the
[first-order characterization of convexity](first-order-conditions-for-convexity/convex-on-iff-forall-add-fderiv-le.md).

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, §3.1.3, eq. (3.2).
- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Measures, integration, derivative, holomorphy), problem `ma_proofbench_l1_95`.
