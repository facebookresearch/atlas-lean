# Measurability of the transformed density candidate

Let $E$ be a finite-dimensional real normed space with its Borel σ-algebra and $\mu$ an additive Haar measure on $E$. Let $T : E \to E$ be a measurable bijection with measurable inverse such that $T^{-1}$ has Fréchet derivative $S'(x)$ at every $x \in E$. Let $Z : \Omega \to E$ be any map on a measure space $(\Omega, \mathbb{P})$, and let $p_Z = d(Z_{\#}\mathbb{P})/d\mu$ be the Radon–Nikodym derivative of the pushforward $Z_{\#}\mathbb{P}$ with respect to $\mu$. Then

$$x \mapsto p_Z(T^{-1}(x))\, \lvert \det S'(x) \rvert$$

is $\mu$-almost everywhere measurable.

No density is assumed. The function $p_Z$ is the density of the absolutely continuous part of $Z_{\#}\mathbb{P}$ with respect to $\mu$ when a Lebesgue decomposition exists, and $0$ otherwise, so it need not represent the whole law: on $E = \mathbb{R}$ with Lebesgue measure, a constant map $Z$ under a probability measure has a point mass as pushforward, which has no density, and $p_Z = 0$ almost everywhere. In dimension $0$ this fails: there a point mass is a multiple of Haar measure and has a constant density. The pushforward $Z_{\#}\mathbb{P}$ is taken to be the zero measure when $Z$ is not almost everywhere measurable.
