# Parseval's identity on the circle

Let $T > 0$ and let $\mu$ be the Haar measure on the circle $\mathbb{R}/T\mathbb{Z}$, normalized to be a probability measure. For every $f \in L^2(\mathbb{R}/T\mathbb{Z}, \mu; \mathbb{C})$, with Fourier coefficients $\hat f(n) = \int e^{-2\pi i n t / T} f(t)\, d\mu(t)$ for $n \in \mathbb{Z}$, the family $(|\hat f(n)|^2)_{n \in \mathbb{Z}}$ is summable and

$$\sum_{n \in \mathbb{Z}} |\hat f(n)|^2 = \int |f(t)|^2 \, d\mu(t).$$

Since $\mu$ has total mass $1$, in terms of Lebesgue measure on a period this reads $\int_{-T/2}^{T/2} |f(t)|^2\,dt = T \sum_{n} |\hat f(n)|^2$.

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014 (free version v1.1), <https://fourierandwavelets.org/FSP_v1.1_2014.pdf>, Section 4.5.2, Theorem 4.15(ii), the Parseval equality (4.104a) (p. 384).
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842: `hasSum_sq_fourierCoeff`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Fourier/AddCircle.lean#L436-L449.
