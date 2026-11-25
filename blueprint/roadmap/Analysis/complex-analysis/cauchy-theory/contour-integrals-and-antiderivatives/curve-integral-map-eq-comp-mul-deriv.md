# Change of variables in a complex line integral

Let `φ` be holomorphic on an open set `Ω` and let `γ` be a curve in `Ω`, differentiable at almost
every time (this covers piecewise differentiable curves, which may have corners). Then for every
`f : ℂ → ℂ`,

$$\int_{\varphi(\gamma)} f(w)\,dw = \int_\gamma f(\varphi(z))\,\varphi'(z)\,dz.$$

The image curve `φ(γ)` is the path `γ.map' _`, and the 1-form `f(w) dw` is
`f w • ContinuousLinearMap.id ℂ ℂ`.
