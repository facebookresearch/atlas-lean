# Naturality of exterior differentiation

Let $F:M\to N$ be a smooth map between finite-dimensional smooth real manifolds without boundary, and let $\omega$ be a smooth real-valued $k$-form on $N$, with $k\geq 0$. Then exterior differentiation commutes with pullback: at every $x\in M$ there is an equality of alternating $(k+1)$-covectors on $T_xM$,

$$
\bigl(d_M(F^*\omega)\bigr)_x=\bigl(F^*(d_N\omega)\bigr)_x.
$$

Here $d_M$ and $d_N$ differentiate forms on their respective manifolds. For any $j$-form $\eta$ on $N$, pullback uses the tangent map in **every** slot:

$$
(F^*\eta)_x(v_1,\ldots,v_j)=\eta_{F(x)}(dF_x v_1,\ldots,dF_x v_j).
$$

For $j=0$ this is composition with $F$, so the degree-zero assertion is the chain rule for a function. The dimensions of $M$ and $N$ may differ, and $dF_x$ can have any rank. The identity is about arbitrary smooth maps, not just changes of chart or restrictions to open subsets.

## Proof sketch

Fix $x$ and choose charts $a$ at $x$ and $b$ at $F(x)$. Restrict the source chart to the inverse image of the target chart's domain, so that $h=b\circ F\circ a^{-1}$ maps one Euclidean open set into the other. Write $\beta=(b^{-1})^*\omega$ for the target representative.

In finite-dimensional real charts a tangent vector acts on smooth functions by directional differentiation. If its coordinate vector is $u$ at $z=a(x)$, then differentiating $g\circ F$ along it gives the derivative of $g\circ b^{-1}$ along $Dh_z u$, by the chain rule. Thus the description of $dF_x$ on point derivations and the tangent map used in the slots give the same coordinate vector. Applying this in every slot identifies the source representative of $F^*\omega$ with $h^*\beta$.

Exterior differentiation in a chart differentiates its representative. The two sides therefore have representatives $d(h^*\beta)$ and $h^*(d\beta)$. The within-set pullback identity on these open sets makes them equal. Transport the covectors back by the source chart differential: they agree at $x$, and hence at every point. Only the charts were inverted, never $F$.

## Depends on

- [Global Forms](../../AlgebraicGeometry/not-yet-classified/manifold-differential-forms/global-forms.md)
- [Rough Form](../../AlgebraicGeometry/not-yet-classified/manifold-differential-forms/rough-form.md)
- [Exterior Derivative](../../AlgebraicGeometry/not-yet-classified/manifold-differential-forms/exterior-derivative.md)
- [Differential of a smooth map at a point, acting on derivations](differential-smooth-map.md)

## Proof depends on

- [Chart Form](../../AlgebraicGeometry/not-yet-classified/manifold-differential-forms/chart-form.md)
- [Exterior differentiation of a pullback within a set](../../Analysis/calculus-in-normed-spaces/exterior-derivative-pullback-within.md)

## Sources

- Lorenzo Sadun, [*Lecture Notes on Differential Forms*](https://arxiv.org/pdf/1604.07862v1), arXiv:1604.07862v1 (2016), p. 7, Theorem 3.1(3) for Euclidean open sets; p. 10, the chart definition of exterior differentiation and (10) for pullback.
- Reyer Sjamaar, [*Manifolds and Differential Forms*](https://pi.math.cornell.edu/~sjamaar/manifolds/manifold.pdf), revised edition (2017), Theorem 3.11, pp. 41–42, for the open-set identity; §7.2, pp. 98–99, for evaluation on tangent vectors.
- Roadmap context: the [Tau Ceti differential geometry roadmap, §1.2](https://github.com/TauCetiProject/TauCetiRoadmap/blob/8cc2f79f60ebc394160c214a3d0abd16c3c0aff9/TauCetiRoadmap/DifferentialGeometry/README.md#L886-L888) treats naturality for a twice continuously differentiable map and a once continuously differentiable form. The smooth scalar case above is a special case.
