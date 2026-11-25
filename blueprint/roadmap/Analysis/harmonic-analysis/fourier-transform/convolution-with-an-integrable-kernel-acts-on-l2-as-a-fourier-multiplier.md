# Convolution with an integrable kernel acts on L² as a Fourier multiplier

Let $h \in L^1(\mathbb{R})$ and $u \in L^2(\mathbb{R})$, and let $\mathcal{F}$ be the Fourier transform on $L^2(\mathbb{R})$ and $\hat h(\omega) = \int h(t) e^{-i\omega t}\, dt$. Then:

1. **Young's inequality.** The convolution $(h * u)(t) = \int h(s)\, u(t - s)\, ds$ converges absolutely for almost every $t$, defines an element of $L^2(\mathbb{R})$, and $\|h * u\|_2 \le \|h\|_1 \|u\|_2$;
2. **Convolution theorem.** $\mathcal{F}(h * u) = \hat h \cdot \mathcal{F} u$ almost everywhere.

So the linear time-invariant system with integrable impulse response $h$ maps finite-energy inputs to finite-energy outputs, with gain at most $\|h\|_1$, and acts in frequency as multiplication by the bounded continuous function $\hat h$.

## Expansion

Part 1 follows from Minkowski's integral inequality, or from Cauchy–Schwarz applied to $|h(s)|^{1/2} \cdot |h(s)|^{1/2}|u(t - s)|$ and Tonelli's theorem, which gives $\int |h * u|^2 \le \|h\|_1 \int\!\!\int |h(s)|\,|u(t - s)|^2\, ds\, dt = \|h\|_1^2\|u\|_2^2$. Part 2 holds for $u \in L^1 \cap L^2$ by the integrable convolution theorem $\widehat{h * u} = \hat h \hat u$ together with the agreement of $\mathcal{F}$ and the integral transform on $L^1 \cap L^2$; both sides are continuous in $u$ from $L^2$ to $L^2$, by part 1 and Plancherel's theorem on the left and by $|\hat h| \le \|h\|_1$ on the right, so density of $L^1 \cap L^2$ extends it. The prerequisites are Plancherel's theorem on $\mathbb{R}$ and the agreement of the two transforms on $L^1 \cap L^2$.

## Depends on

- [The L² Fourier transform agrees with the Fourier integral on L¹ ∩ L²](the-l2-fourier-transform-agrees-with-the-fourier-integral-on-l1-cap-l2.md): the $L^2$ transform on $L^1 \cap L^2$

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014, <https://www.fourierandwavelets.org/>, Section 4.4.3: convolution in time corresponds to multiplication of Fourier transforms (4.62), proved for $h, x \in L^1(\mathbb{R})$ (p. 369), Parseval's equality (4.71) on $L^2(\mathbb{R})$ (p. 371), and Theorem 4.8 on bounded-input bounded-output stability of filters with integrable impulse response; Section 4.4.2 on the extension of the transform to $L^2(\mathbb{R})$ (p. 363).
