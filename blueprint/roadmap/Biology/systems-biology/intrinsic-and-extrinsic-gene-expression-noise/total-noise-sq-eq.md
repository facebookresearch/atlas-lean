# Total noise splits into intrinsic and extrinsic parts

Let $(\Omega, \mathcal{F})$ be a measurable space with a probability measure $\mu$, let $m \subseteq \mathcal{F}$ be a sub-σ-algebra (the extrinsic information), and let $X, Y \colon \Omega \to \mathbb{R}$ be square-integrable reporters forming an [identical reporter pair](is-identical-reporter-pair.md) given $m$. Then the [total noise strength](total-noise-sq.md) is
$\eta_{\mathrm{tot}}^2 = \operatorname{Var}(X)/\mathbb{E}[X]^2$, with the quotient read as $0$ when
$\mathbb{E}[X] = 0$. By the law of total variance,
$\operatorname{Var}(X) = \mathbb{E}[\operatorname{Var}(X \mid m)] + \operatorname{Var}(\mathbb{E}[X \mid m])$,
so it splits into the [intrinsic](intrinsic-noise-sq-eq.md) and [extrinsic](extrinsic-noise-sq-eq.md)
parts.
