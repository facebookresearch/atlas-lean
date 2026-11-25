# Infinite beam on a Winkler foundation under a point load

Let an infinite Euler–Bernoulli beam with $EI > 0$ rest on a Winkler foundation of modulus $k > 0$ (force per length per deflection) and
carry a signed point load $P \in \mathbb R$ at $x = 0$. Put $\beta = (k/(4EI))^{1/4}$. The deflection that solves $EI\,w'''' + k w = 0$ for $x \ne 0$, is bounded
and decays as $\lvert x\rvert \to \infty$, has continuous $w$, $w'$ and $w''$ at $x = 0$, and satisfies $EI\,(w'''(0^+)-w'''(0^-))=P$, is

$$w(x) = \frac{P\beta}{2k}\,e^{-\beta\lvert x\rvert}\bigl(\cos\beta\lvert x\rvert + \sin\beta\lvert x\rvert\bigr).$$

The jump convention is the one in $EI\,w''''+kw=P\delta_0$. Symmetry gives $w'(0)=0$ and $EI\,w'''(0^+)=P/2$. If shear is defined
as $V=-EI\,w'''$, its jump is $-P$. A periodic cosine flexure profile is a different result.

## Depends on

## Proof depends on

## Sources

- Q. P. Sun, lecture notes, Chapter 4, *Elastic foundations*, Sections 4.1–4.3: the Winkler foundation, governing equation and the infinite beam under a concentrated load with $\beta = (k/4EI)^{1/4}$, HKUST, <https://mae.hkust.edu.hk/~meqpsun/Notes/CHAPTER4.pdf>.
