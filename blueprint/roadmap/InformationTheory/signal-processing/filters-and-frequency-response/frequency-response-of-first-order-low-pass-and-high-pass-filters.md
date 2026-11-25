# Frequency response of first-order low-pass and high-pass filters

Let $\tau > 0$ and, for $\omega \in \mathbb{R}$, let

$$H_L(i\omega) = \frac{1}{1 + i\omega\tau}, \qquad H_H(i\omega) = 1 - H_L(i\omega) = \frac{i\omega\tau}{1 + i\omega\tau}$$

be the frequency responses of the first-order low-pass filter $1/(1 + s\tau)$ and the complementary high-pass filter $s\tau/(1 + s\tau)$. Then:

1. **Gains.** $|H_L(i\omega)|^2 = \dfrac{1}{1 + \omega^2\tau^2}$ and $|H_H(i\omega)|^2 = \dfrac{\omega^2\tau^2}{1 + \omega^2\tau^2}$. Both lie in $[0, 1]$ and sum to $1$. Moreover $|H_L| \to 1$ and $|H_H| \to 0$ as $\omega \to 0$, while $|H_L| \to 0$ and $|H_H| \to 1$ as $|\omega| \to \infty$.
2. **Phases.** $\arg H_L(i\omega) = -\arctan(\omega\tau) \in (-\pi/2, \pi/2)$. For $\omega \ne 0$, $\arg H_H(i\omega) = \arctan\big(1/(\omega\tau)\big)$, which is positive for $\omega > 0$ and negative for $\omega < 0$. At $\omega = 0$, $H_H = 0$ and no phase is assigned.
3. **Corner.** Both gains equal $1/\sqrt{2}$ (half power) exactly at $|\omega| = 1/\tau$, where the phases are $\mp\pi/4$ and $\pm\pi/4$ for $\omega = \pm 1/\tau$.
4. **Asymptotes.** In decibels, $20\log_{10}|H_L(i\omega)| = -10\log_{10}(1 + \omega^2\tau^2)$. This tends to $0$ as $\omega \to 0$, and as $|\omega| \to \infty$ it differs from $-20\log_{10}(|\omega|\tau)$ by a term tending to $0$, a slope of $-20$ dB per decade. Symmetrically, $20\log_{10}|H_H(i\omega)|$ differs from $20\log_{10}(|\omega|\tau)$ by a term tending to $0$ as $\omega \to 0$, and tends to $0$ as $|\omega| \to \infty$.

Each item is direct complex arithmetic with $H_L = (1 - i\omega\tau)/(1 + \omega^2\tau^2)$ and $H_H = (\omega^2\tau^2 + i\omega\tau)/(1 + \omega^2\tau^2)$. For the high-pass phase with $\omega \ne 0$, note that $H_H = \omega\tau\,(\omega\tau + i)/(1 + \omega^2\tau^2)$.

## Sources

- K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*, 2nd ed., Princeton University Press, 2021 (electronic edition v3.0i, <http://fbsbook.org>), Section 9.6, Bode plots of the first-order system $G(s) = a/(s + a)$, with breakpoint at $\omega = a$ and asymptotes for gain and phase (Figure 9.14a and the straight-line approximations that follow it, p. 9-32), here with $a = 1/\tau$.
