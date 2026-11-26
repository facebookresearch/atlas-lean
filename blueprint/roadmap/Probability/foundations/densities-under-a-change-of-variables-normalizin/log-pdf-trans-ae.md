# Composition adds log-determinants

Let $E$ be a finite-dimensional real normed space with its Borel σ-algebra and $\mu$ an additive Haar measure on $E$. Let $T_1, T_2 : E \to E$ be measurable bijections with measurable inverses such that $T_1^{-1}$ and $T_2^{-1}$ have Fréchet derivatives $S_1'(x)$ and $S_2'(x)$ at every $x$. Let $Z : \Omega \to E$ be a random variable on $(\Omega, \mathbb{P})$ with a density $p_Z$ with respect to $\mu$, and let $p_X$ be the density of $X = T_2 \circ T_1 \circ Z$. Then for $\mu$-almost every $x \in E$: writing $u = T_1^{-1}(T_2^{-1}(x))$, if $0 < p_Z(u) < \infty$, $\det S_1'(T_2^{-1}(x)) \ne 0$ and $\det S_2'(x) \ne 0$, then

$$\log p_X(x) = \log p_Z(u) + \log \lvert \det S_1'(T_2^{-1}(x)) \rvert + \log \lvert \det S_2'(x) \rvert.$$
