# The dual of L^1 for a σ-finite measure

Let $(X, \mathcal{M}, \mu)$ be a σ-finite measure space, with real or complex scalars. For $h \in L^\infty(\mu)$, the
functional $\varphi_h(f) = \int f h \, d\mu$ on $L^1(\mu)$ is bounded with $\|\varphi_h\| = \|h\|_\infty$, and
$h \mapsto \varphi_h$ is a linear bijection of $L^\infty(\mu)$ onto the dual space $(L^1(\mu))'$. So $L^\infty(\mu)$ is
isometrically isomorphic to the dual of $L^1(\mu)$.

## Idea

Hölder's inequality for the exponents $1$ and $\infty$ gives $\|\varphi_h\| \le \|h\|_\infty$, and, for $h \ne 0$,
testing $\varphi_h$ on the function $f$ equal to $\overline{h}/|h|$ on $E$ and to $0$ elsewhere, which has
$\|f\|_1 = \mu(E)$, for sets $E$ of finite positive measure on which $|h| > \|h\|_\infty - \varepsilon$ with
$0 < \varepsilon < \|h\|_\infty$, which exist by σ-finiteness, gives
$|\varphi_h(f)| \ge (\|h\|_\infty - \varepsilon) \|f\|_1$, hence equality. Surjectivity is the substance: for a bounded
functional $\varphi$ on $L^1(\mu)$ and finite $\mu$, $E \mapsto \varphi(\chi_E)$ is a real or complex measure absolutely
continuous with respect to $\mu$, and its Radon–Nikodym derivative is bounded by $\|\varphi\|$ and represents $\varphi$;
σ-finiteness lets one patch these derivatives together. Without σ-finiteness the map can fail to be onto. In the other
direction, $L^1$ is not the dual of $L^\infty$ in general: the dual of $\ell^\infty$ is larger than $\ell^1$.

## Statements

- [The dual of $L^1$ is $L^\infty$ for a σ-finite measure](l1-dual-sigma-finite.md)

## Background

- [L^p spaces](../../normed-and-ordered-structure-of-lp-spaces/lp-space-of-a-measure/README.md): $L^1$ and $L^\infty$
- [Hölder's inequality](../../h-lder-and-minkowski-inequalities-for-integrals/h-lder-s-inequality/README.md): the bound $\|\varphi_h\| \le \|h\|_\infty$
- [Measures](../../../measures/measures-and-countable-additivity/measures/README.md): σ-finite measures

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, result 9.42, the case $p = 1$ (version read: the open-access PDF dated 12 June 2026).
