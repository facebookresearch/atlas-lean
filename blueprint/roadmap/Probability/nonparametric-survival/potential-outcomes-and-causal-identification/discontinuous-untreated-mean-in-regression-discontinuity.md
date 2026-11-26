# A discontinuous untreated mean produces a jump with no treatment effect

In a sharp regression-discontinuity design with cutoff zero, the running variable $X$ is uniform on $[-1,1]$ and treatment is assigned exactly when $X\ge 0$. Every interval $(0,\varepsilon)$ and $(-\varepsilon,0)$ with $\varepsilon>0$ has positive probability. Set both potential outcomes to $\mathbf 1\{X\ge 0\}$, so the treatment effect is zero for every unit.

The step function $m(x)=\mathbf 1\{x\ge 0\}$ is a version of the conditional mean of either potential outcome given $X=x$. The observed outcome equals both potential outcomes, so its conditional mean has the same version. The right limit of $m$ at zero is $1$ and its left limit is $0$. The observed regression therefore jumps by one even though no unit has a treatment effect.

## Background

- [Identification in the sharp regression-discontinuity design](../../not-yet-classified/part-13/regression-discontinuity/sharp-rd-identification.md): continuity of both potential-outcome regression functions at the cutoff, together with support on both sides, identifies the cutoff effect from the observed jump.

## Sources

- G. W. Imbens and T. Lemieux, "Regression discontinuity designs: a guide to practice", NBER Working Paper 13039, 2007, §2.2 and Assumption 2.1, <https://www.nber.org/papers/w13039>: the continuity assumption and cutoff identification. The step-function counterexample is derived here.
