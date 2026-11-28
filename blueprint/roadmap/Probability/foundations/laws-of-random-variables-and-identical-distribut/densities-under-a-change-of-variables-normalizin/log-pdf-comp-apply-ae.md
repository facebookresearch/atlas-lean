# Log-likelihood of a normalizing flow, forward form

Let $E$ be a finite-dimensional real normed space with its Borel σ-algebra and $\mu$ an additive Haar measure on $E$. Let $T : E \to E$ be a measurable bijection with measurable inverse such that $T^{-1}$ has Fréchet derivative $S'(x)$ at every $x \in E$. Assume also that $T$ has Fréchet derivative $T'(z)$ at every $z \in E$. Let $Z : \Omega \to E$ be a random variable on $(\Omega, \mathbb{P})$ that has a density with respect to $\mu$ ($Z$ is a.e. measurable and its law is absolutely continuous with respect to $\mu$), write $p_Z = d(Z_{\#}\mathbb{P})/d\mu$, and let $X = T \circ Z$ with density $p_X = d(X_{\#}\mathbb{P})/d\mu$. Then for $\mu$-almost every $z \in E$ with $0 < p_Z(z) < \infty$,

$$\log p_X(T(z)) = \log p_Z(z) - \log \lvert \det T'(z) \rvert.$$
