# Angular-frequency wave multipliers

On $\mathbb R^n$ with Euclidean scalar product and Lebesgue measure, use $\widehat f(\xi)=\int e^{-ix\cdot\xi}f(x)\,dx$ and $\mathcal F^{-1}g(x)=(2\pi)^{-n}\int e^{ix\cdot\xi}g(\xi)\,d\xi$. For real $t,s,B$ the half-wave $U(t)$, the Bessel operator $J^s$, and $J^s[\log(2+J)]^B$ are defined by applying this inverse transform after multiplication by $e^{-it|\xi|}$, $(1+|\xi|^2)^{s/2}$, and $(1+|\xi|^2)^{s/2}[\log(2+\sqrt{1+|\xi|^2})]^B$, respectively. Time observation is product Lebesgue measure with the time factor restricted to the closed interval $[1,2]$. This convention uses angular rather than cyclic frequency.

## Sources

- [Definitions in `Definitions.lean`, lines 21–53](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/LocalSmoothing/Definitions.lean#L21-L53).
- [Definitions in `Basic.lean`, lines 8–11](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Wave/Basic.lean#L8-L11).
