# Frequency response of the discrete-time one-pole filter

Let $0 < a < 1$. Consider the causal filter $y(k+1) = a\, y(k) + (1 - a)\, u(k)$ for $k \in \mathbb{Z}$, started at rest, so that its impulse response is $h_0 = 0$ and $h_k = (1 - a) a^{k-1}$ for $k \ge 1$. Then $h \in \ell^1(\mathbb{Z})$ and, for $\theta \in \mathbb{R}$, its frequency response $H(e^{i\theta}) = \sum_k h_k e^{-ik\theta}$ is:

1. $H(e^{i\theta}) = \dfrac{(1 - a)\, e^{-i\theta}}{1 - a e^{-i\theta}}$;
2. the dc gain is $H(1) = 1$;
3. $|H(e^{i\theta})|^2 = \dfrac{(1 - a)^2}{1 - 2a\cos\theta + a^2}$, which is strictly decreasing in $\theta \in [0, \pi]$, from $1$ at $\theta = 0$ to $\left(\frac{1 - a}{1 + a}\right)^2$ at $\theta = \pi$.

Formulas 1 and 2 hold for every real $a$ with $|a| < 1$, and so does the expression in part 3. For $-1 < a < 0$, $|H|$ is instead strictly increasing on $[0, \pi]$.

Part 1 sums the geometric series $\sum_{k \ge 1} (1 - a) a^{k-1} e^{-ik\theta}$, which converges absolutely because $|a| < 1$. Part 3 uses $|1 - a e^{-i\theta}|^2 = 1 - 2a \cos\theta + a^2$, and the denominator is strictly increasing on $[0, \pi]$ when $a > 0$.

## Depends on

- [Discrete-time Fourier transform of absolutely summable sequences](../../../Analysis/harmonic-analysis/fourier-transform/discrete-time-fourier-transform-of-summable-sequences.md): the frequency response is the transform of the absolutely summable impulse response

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014 (free version v1.1), <https://fourierandwavelets.org/FSP_v1.1_2014.pdf>, Section 3.4: the transform pair $\alpha^n u_n \leftrightarrow 1/(1 - \alpha e^{-j\omega})$ for $|\alpha| < 1$ and the shift property (Table 3.4, p. 222), and Section 3.4.4, frequency response of filters (from p. 227).
