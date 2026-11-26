# Change of variables in a complex line integral

Let `φ` be holomorphic on an open set `Ω` and let `γ` be a curve in `Ω`, differentiable at almost
every time (this covers piecewise differentiable curves, which may have corners). Then for every
`f : ℂ → ℂ`,

$$\int_{\varphi(\gamma)} f(w)\,dw = \int_\gamma f(\varphi(z))\,\varphi'(z)\,dz.$$

The image curve `φ(γ)` is the path `γ.map' _`, and the 1-form `f(w) dw` is
`f w • ContinuousLinearMap.id ℂ ℂ`. A curve integral is the integral of the pulled-back form over the parameter interval, read as `0` when that integrand is not integrable; so the identity holds for every `f`, but both sides may be this `0` rather than a convergent classical integral (for example `f(z) = 1/z` along the identity path from `0` to `1`).
