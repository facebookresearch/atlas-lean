# Exterior differentiation of a pullback within a set

Let $\mathbb K$ be a nontrivially normed field, and let $E,V,G$ be normed $\mathbb K$-vector spaces. Fix $n\in\mathbb N$ (including zero), sets $s\subseteq E$ and $t\subseteq V$, a map $f:E\to V$, and a field $\omega$ on $V$ whose value at each point is a continuous alternating $\mathbb K$-multilinear map $V^n\to G$. At $x\in E$ suppose that:

- $f(s)\subseteq t$, $s$ has unique differentials over $\mathbb K$ (`UniqueDiffOn`), and $x\in s\cap\overline{\operatorname{int}(s)}$;
- $\omega$, as a map into the normed space of such alternating maps, is differentiable over $\mathbb K$ within $t$ at $f(x)$;
- $f$ is $C^r$ over $\mathbb K$ within $s$ at $x$, where $r$ is a differentiability order (finite, smooth, or analytic) and $r\geq\operatorname{minSmoothness}(\mathbb K,2)$. This threshold is $2$ for a real- or complex-like normed field (`IsRCLikeNormedField`), and the analytic order otherwise.

Write $D_s f(y)$ for the Fréchet derivative within $s$ at $y$, and $d_s,d_t$ for exterior differentiation within the indicated sets (the alternating sum formed from the respective within-set Fréchet derivatives). For an alternating map $A$ of degree $j$ and a continuous linear map $L$, write $A[L]$ for precomposition by $L$ in all $j$ slots. Define the field $P(y)=\omega(f(y))[D_s f(y)]$. Then, as continuous alternating $(n+1)$-linear maps $E^{n+1}\to G$,

$$
(d_s P)(x)=(d_t\omega)(f(x))[D_s f(x)].
$$

The derivative inside $P$ varies with $y$; the one on the right is evaluated at $x$. No unique-differentials assumption on $t$ is required.

## Application in charts

For a smooth real map in coordinates, take $s$ to be the open source of the coordinate representative, restricted so that the map takes it into the target open set $t$. Every point of $s$ is interior, unique differentials hold there, and smoothness gives the required order and the differentiability of the form. Values assigned to the representatives outside these open sets do not affect the within-set calculation. The identity therefore compares the coordinate forms without requiring a globally defined smooth extension of either representative.

## Sources

- The mathlib Community, [`extDerivWithin_pullback`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean#L239-L245), in `Mathlib.Analysis.Calculus.DifferentialForm.Basic`; [scalar and space assumptions](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean#L53-L59) and [definition of the smoothness threshold](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean#L491-L502) at the same revision.
- Roadmap context: the [Tau Ceti differential geometry roadmap, §1.1](https://github.com/TauCetiProject/TauCetiRoadmap/blob/8cc2f79f60ebc394160c214a3d0abd16c3c0aff9/TauCetiRoadmap/DifferentialGeometry/README.md#L883-L885) lists this within-set pullback identity as an ingredient in chart calculations. The general normed-field statement above is the Mathlib result.
