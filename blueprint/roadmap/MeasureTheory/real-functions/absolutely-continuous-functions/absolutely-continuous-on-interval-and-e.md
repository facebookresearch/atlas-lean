# A $1$-Lipschitz function on $(a,b)$ is absolutely continuous with essentially bounded derivative

**A $1$-Lipschitz function on $[a,b]$ is absolutely continuous with essentially bounded
derivative.** Let $a \le b$ be real numbers and let $f : \mathbb{R} \to \mathbb{R}$ satisfy
$|f(x) - f(y)| \le |x - y|$ for all $x, y \in [a, b]$. Then $f$ is absolutely continuous on
$[a, b]$, and its derivative $f'$, taken to be $0$ at points where $f$ is not differentiable, has
finite norm $\|f'\|_{L^\infty[a,b]}$, the essential supremum with respect to Lebesgue measure on
$[a, b]$.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of one variable), `benchmark/level1/ma_proofbench_l1_34.lean` at openbmb/ma-proofbench@31bab4c.
