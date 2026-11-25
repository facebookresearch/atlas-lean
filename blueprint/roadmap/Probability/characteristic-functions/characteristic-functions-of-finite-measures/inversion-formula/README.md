# Inversion formula for characteristic functions

A probability measure $\mu$ on $\mathbb R$ is recovered from its characteristic function $\varphi$: for $a < b$,
$\lim_{T \to \infty} \frac{1}{2\pi} \int_{-T}^{T} \frac{e^{-ita} - e^{-itb}}{it} \, \varphi(t) \, dt = \mu((a, b)) + \frac12 \mu(\{a, b\})$.

## Idea

When $a$ and $b$ are not atoms of $\mu$, the right side is $\mu((a, b])$, and these values determine $\mu$;
so two probability measures with the same characteristic function are equal. The factor
$\frac{e^{-ita} - e^{-itb}}{it} = \int_a^b e^{-ity} \, dy$ is the Fourier transform of the indicator of $[a, b]$, which
makes the formula a Fourier inversion. The limit cannot be replaced by an absolutely convergent integral in general:
for the point mass at $0$, $\varphi \equiv 1$, and with $a = -1$, $b = 1$ the integrand is $2 \sin t / t$.

## Statements

- [Inversion formula for characteristic functions](levy-inversion-formula.md)

## Background

- [Characteristic function](../characteristic-function/README.md): characteristic functions
