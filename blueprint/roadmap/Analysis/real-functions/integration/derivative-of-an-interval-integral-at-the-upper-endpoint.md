# Derivative of an interval integral at the upper endpoint

Let $E$ be a complete real normed vector space, $f:\mathbb R\to E$, and $a,b\in\mathbb R$. Use Lebesgue measure. Suppose that:

- $f$ is interval-integrable between $a$ and $b$: it is integrable on $(a,b]$ and on $(b,a]$, of which at most one is nonempty;
- on some neighbourhood $U$ of $b$, $f$ agrees almost everywhere, for Lebesgue measure restricted to $U$, with a strongly measurable function $\mathbb R\to E$;
- $f$ is continuous at $b$.

Then the function $F(u)=\int_a^u f(x)\,dx$ has derivative $f(b)$ at $u=b$. Here the lower endpoint is fixed and the upper endpoint varies on the real line: the conclusion is a two-sided derivative even if $a=b$ or $b<a$. The local measurability hypothesis is `StronglyMeasurableAtFilter` at the neighbourhood filter of $b$; it does not ask for strong measurability everywhere.

## Sources

- Mathlib, [`intervalIntegral.integral_hasDerivAt_right`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean#L725 "intervalIntegral.integral_hasDerivAt_right").
- For an application to regular curves, see [Tau Ceti’s geometric measure theory roadmap, G1](https://github.com/TauCetiProject/TauCetiRoadmap/blob/8cc2f79f60ebc394160c214a3d0abd16c3c0aff9/TauCetiRoadmap/GeometricMeasureTheory/README.md#L106-L139): differentiating the arc-length coordinate recovers the speed.
