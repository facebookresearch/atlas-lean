# Oriented interval integral

Let $\mu$ be a measure on the Borel sets of $\mathbb R$, let $E$ be a real normed vector space, and let $f:\mathbb R\to E$. For real endpoints $a,b$, the oriented interval integral is the difference of two Bochner set integrals:

$$
\int_a^b f\,d\mu
=\int_{(a,b]} f\,d\mu-\int_{(b,a]} f\,d\mu.
$$

For $a<b$ only the first interval is nonempty: it excludes $a$ and includes $b$, a distinction that matters if $\mu$ has atoms. Interchanging the endpoints negates the integral; equal endpoints give zero. The definition requires neither integrability nor completeness of $E$. It uses the convention that a set integral is zero if the function is not integrable for the restricted measure, or if the target space is not complete.

## Sources

- Mathlib, [`intervalIntegral`](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean#L664 "intervalIntegral").
- For the regular-curve application to signed arc length, see [Tau Ceti’s geometric measure theory roadmap, G1](https://github.com/TauCetiProject/TauCetiRoadmap/blob/8cc2f79f60ebc394160c214a3d0abd16c3c0aff9/TauCetiRoadmap/GeometricMeasureTheory/README.md#L106-L139).
