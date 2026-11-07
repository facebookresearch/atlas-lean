# Lipschitz functions are the absolutely continuous functions with bounded derivative

Let
$f : \mathbb{R} \to \mathbb{R}$ and let $M \ge 0$ be a real number. Then
$|f(x) - f(y)| \le M|x - y|$ for all $x, y \in \mathbb{R}$ if and only if $f$ is absolutely
continuous on every closed bounded interval and $|f'(x)| \le M$ for almost every $x \in \mathbb{R}$
(with respect to Lebesgue measure), where $f'(x)$ is taken to be $0$ at points where $f$ is not
differentiable.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of one variable), `benchmark/level1/ma_proofbench_l1_62.lean` at openbmb/ma-proofbench@31bab4c.
