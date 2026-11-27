# Approximating modular reduction by a scaled sine

Let $q>0$, $I\in\mathbb{Z}$, and $t=qI+r$ with $|r|\le\epsilon q$ for $\epsilon< 1/4$. Then

$$
\Bigl|r-\frac{q}{2\pi}\sin\Bigl(\frac{2\pi t}{q}\Bigr)\Bigr|\le\frac{2\pi^{2}}{3}\cdot\frac{|r|^{3}}{q^{2}}\le\frac{2\pi^{2}}{3}\epsilon^{2}|r|.
$$

Hence $\frac{q}{2\pi}\sin(2\pi t/q)$ computes $t\bmod q$ with relative error $O(\epsilon^{2})$ when the message is small compared to $q$; the sine (or cosine) is evaluated homomorphically by a low-degree Taylor or Chebyshev approximation on a small interval followed by repeated double-angle formulas.

## Proof sketch

By periodicity $\sin(2\pi t/q)=\sin(2\pi r/q)$. For real $x$, $0\le x-\sin x\le x^{3}/6$ when $x\ge 0$ (and symmetrically for $x<0$). With $x=2\pi r/q$, multiplying by $q/(2\pi)$ gives the error bound $(q/2\pi)(2\pi|r|/q)^{3}/6=(2\pi^{2}/3)|r|^{3}/q^{2}$.

## Proof depends on

- [ModRaise introduces a small integer multiple of the base modulus](ckks-modraise.md)

## Sources

- Jung Hee Cheon, Kyoohyung Han, Andrey Kim, Miran Kim, Yongsoo Song, "Bootstrapping for Approximate Homomorphic Encryption", EUROCRYPT (2018).
