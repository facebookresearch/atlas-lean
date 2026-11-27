# A weak Hessian upper bound along every prescribed RCD geodesic

Let $(X,d)$ be complete separable with a Borel measure $m$ of full support, finite on bounded sets, satisfying $\mathrm{RCD}(K,N)$ for $K,N\in\mathbb R$, $N>1$. Use unreduced $\mathrm{CD}(K,N)$: for absolutely continuous probability endpoints with finite second moment there is a dynamical optimal quadratic-cost coupling satisfying the Rényi entropy inequality for all $N'\ge N$ with $\tau_{K,N'}$ distortion coefficients. Require quadratic Cheeger energy (the $L^2$ relaxation of half the squared local Lipschitz slope).

Let $F$ be bounded and globally Lipschitz and $G$ bounded and continuous. Use the following integrated local gradient convention. A test plan $\pi$ is a probability measure on continuous paths $\gamma:[0,1]\to X$, with one compression bound $(e_t)_*\pi\le C m$ for all evaluation times, concentrated on absolutely continuous paths with square-integrable metric control, and with finite averaged kinetic energy $\int\!\int_0^1|\dot\gamma|^2\,dt\,d\pi$. Use the limsup of the distance quotient for the metric speed, with the path clamped outside $[0,1]$. For the local gradient test, require in addition that there is one closed ball containing the whole track of $\pi$-almost every path. A real $D$ is a local weak upper gradient of $f$ if $D\ge0$ almost everywhere and $D\in L^2$ on every positive-radius open ball, and for every such bounded-track plan it satisfies

$$\int |f(\gamma(1))-f(\gamma(0))|\,d\pi(\gamma)\le\int\!\int_0^1 D_+(\gamma(t))|\dot\gamma|(t)\,dt\,d\pi(\gamma).$$

Choose an almost-everywhere minimal such $D$ if one exists, and use the zero function if none exists. Denote the resulting representative by $D_f$ and write $\Gamma(u,v)=(D_{u+v}^2-D_{u-v}^2)/4$. The Sobolev class used in the generator requires $f$ and $D_f$ in global $L^2$ and existence of a minimal local gradient. The generator $\Delta g$ is a chosen $L^2$ representative satisfying $\int\Gamma(g,v)\,dm=-\int (\Delta g)v\,dm$ for every such Sobolev $v$ when $g$ is in the generator domain, and is set to zero otherwise. For each compactly supported bounded Lipschitz $g$ in that domain with Sobolev Laplacian, and every nonnegative compactly supported globally Lipschitz $h$, assume

$$-\int(\Gamma(h,g)+h\Delta g)\Gamma(F,g)\,dm-\int h\Gamma(F,\Gamma(g,g)/2)\,dm\le\int hG\Gamma(g,g)\,dm.$$

There is no global $L^2$ requirement on $F$. Then for **every** constant-speed minimizing $\sigma:[0,1]\to X$, including constant curves, and every nonnegative smooth test function $\varphi$ compactly supported in $(0,1)$,

$$\int_0^1 (F\circ\sigma)\varphi''\,dt\le d(\sigma(0),\sigma(1))^2\int_0^1 (G\circ\sigma)\varphi\,dt.$$

## Depends on

- Test plans, weak upper gradients and representatives, weak generator, and unreduced CD plus quadratic Cheeger energy.

## Proof depends on

- Regularization and approximation of a prescribed geodesic by test-plan transports satisfying the Hessian estimate, with passage to the distributional inequality.

## Expansion

Prove agreement of the bounded-track test-plan gradient and weak generator with any native RCD realization, including the domains on which the totalized choices represent the usual operators. Verify the compact-support conventions and the sign of the negative energy generator. Prove the passage to every prescribed geodesic rather than almost every curve of a selected transport plan; treat zero-speed curves directly.

## Sources

- OpenAI Math, [`every_geodesic`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/WeakHessian.lean#L218-L228) (statement and local definitions).
- OpenAI Math, [test plans, local weak gradients and generator](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/WeakHessian.lean#L31-L107).
