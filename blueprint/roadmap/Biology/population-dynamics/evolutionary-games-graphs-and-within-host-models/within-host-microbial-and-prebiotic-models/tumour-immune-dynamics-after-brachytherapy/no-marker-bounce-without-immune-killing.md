# No marker bounce without immune killing under decaying radiation

Let a tumour of size $x(t)$ follow the radiation-only model

$$\frac{dx}{dt} = \left(p_1 - s_1 e^{-\lambda t}\right) x, \qquad x(0) = x_0 > 0,$$

with $p_1 > 0$, $s_1 > 0$ and $\lambda > 0$, and let the serum marker concentration $z(t)$ (PSA) be produced by the tumour at rate $p\,x$, released by radiation-killed cells at rate $s e^{-\lambda t} x$, and cleared at rate $u > 0$:

$$\frac{dz}{dt} = \left(p + s e^{-\lambda t}\right) x - u z, \qquad z(0) = z_0,$$

with $p, s \ge 0$ and $p + s > 0$. Call a **bounce** a strict local minimum of $z$ at some time $b > 0$ followed by a strict local maximum at a later time $a > b$ (a transient rise that resolves on its own). Then $z$ has no bounce: there is a time $\tau^\ast \in [0,\infty]$ such that every strict local maximum of $z$ in $(0,\infty)$ lies in $(0, \tau^\ast]$ and every strict local minimum lies in $[\tau^\ast, \infty)$. The possible shapes of $z$ are therefore monotone, fall-then-rise, rise-then-fall, or rise-fall-rise, but never fall-rise-fall.

This precise statement and its proof below are derived on this page; the source does not print them and argues the no-bounce claim only intuitively (see the last paragraph).

## Depends on

- [Tumour burden under exponentially decaying radiation kill](tumour-burden-under-exponentially-decaying-radiation-kill.md)

## Proof depends on

- [Convexity of log-sum-exp with nonnegative nonzero weights](../../../../../StatisticalMechanics/random-cluster-model/convexity-of-the-free-energy-and-edge-densities/ivp2-kcgf-convex-on.md)

## Proof sketch

Write $h(t) = (p + s e^{-\lambda t}) x(t)$ for the marker input, so $z' = h - u z$. Then $\log h = \log(p e^{0 \cdot t} + s e^{-\lambda t}) + \log x$ is a sum of a log-sum-of-exponentials (convex) and the strictly convex $\log x$, hence strictly convex; so $h'$ is negative before a time $\tau^\ast$ and positive after it (with $\tau^\ast = 0$ or $\infty$ allowed). Put $w = z'$, which satisfies $w' = h' - u w$. At a strict local maximum $a$ of $z$, $w$ passes from positive to negative through $w(a) = 0$, and there $w'(a) = h'(a)$; if $h'(a) > 0$ then $w$ would be strictly increasing at $a$, a contradiction, so $h'(a) \le 0$ and $a \le \tau^\ast$. Symmetrically, at a strict local minimum $b$, $h'(b) \ge 0$ and $b \ge \tau^\ast$. Hence $a \le \tau^\ast \le b$ for every such pair, and no local minimum precedes a local maximum.

Yamamoto et al. state that a model with only the radiation-modified tumour equation and the marker equation (their Equations 1a and 3 with the immune term removed, equivalently $\delta = 0$) cannot reproduce a PSA bounce, and that the bounce invariably occurs after the isotope has decayed. Their support is an intuitive argument in the Discussion: once the effect of radiation is over ($s_1 = s = 0$) the equations "only capture exponential growth of the tumour and PSA production", so a two-equation model "will not be able to fit the PSA data showing an initial increase in PSA followed by decay". The theorem and proof above are this page's own derivation, not a result printed in the source; they replace that intuition with a statement valid for all times, including while the radiation term is still active. In their fits to 63 patients the full model with an immune compartment was preferred by a corrected Akaike criterion, and the only parameter differing significantly between patients with and without a bounce was the initial strength of the immune response ($\beta = 2.90$ versus $1.75$, $P = 0.01$), matching higher CD8 T-cell densities in pre-treatment biopsies of bounce patients.

## Sources

- Y. Yamamoto et al., "Tumour and immune cell dynamics explain the PSA bounce after prostate cancer brachytherapy", British Journal of Cancer (2016), <https://doi.org/10.1038/bjc.2016.171> (PMC4947697), Materials and methods, "Mathematical modelling" (Equations 1a and 3), Results, "Model fitting and parameter comparisons", and Discussion (the intuitive no-bounce argument; the precise theorem on this page is derived here, not printed in the source).
