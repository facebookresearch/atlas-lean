# Convolution theorem

Let $e$ be a continuous additive character from $\mathbb{R}$ to the
unit circle, and let $\mu$ be a σ-finite measure on $\mathbb{R}$ that is preserved by every
translation $x \mapsto a + x$. For $\varphi : \mathbb{R} \to \mathbb{C}$ write
$\hat\varphi(w) = \int e(-xw)\,\varphi(x)\,d\mu(x)$ for its Fourier transform with respect to
$e$ and $\mu$, and for $f, g : \mathbb{R} \to \mathbb{C}$ write
$(f * g)(x) = \int f(t)\,g(x - t)\,d\mu(t)$ for their convolution. If $f$ and $g$ are
$\mu$-integrable, then $\widehat{f * g}(w) = \hat f(w)\,\hat g(w)$ for every $w \in \mathbb{R}$.

Proof: Integrability of the convolution integrand, Fubini's theorem, translation invariance of
$\mu$ and multiplicativity of $e$, following Stein--Shakarchi, Ch. 5, Prop. 1.11.

## Sources

- https://en.wikipedia.org/wiki/Convolution_theorem.
