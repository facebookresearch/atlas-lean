# The heat kernel has total mass one

Let $E$ be a finite-dimensional real inner product space, with its Lebesgue measure (the volume of the inner product space), and let $\Phi$ be the [heat kernel](heat-kernel.md) on $E$. For $t > 0$,

$$\int_E \Phi(t, x) \, dx = 1,$$

for the volume of the inner product space (Lebesgue measure on $\mathbb{R}^n$). The computation is
the Gaussian integral $\int_E e^{-b \|x\|^2} dx = (\pi / b)^{n/2}$ with $b = 1/(4t)$.

## Sources

- M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, [Chapter 4 (Heat equation)](https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_4.pdf), Lemma 4.2.
