# Gain and phase of a lead or lag compensator

Let $k, a, b > 0$ and $C(s) = k\,\dfrac{s + a}{s + b}$. For every real $\omega$:

1. $|C(i\omega)| = k \sqrt{\dfrac{\omega^2 + a^2}{\omega^2 + b^2}}$, with $|C(0)| = k a / b$ and $|C(i\omega)| \to k$ as $|\omega| \to \infty$.
2. $\arg C(i\omega) = \arctan(\omega / a) - \arctan(\omega / b)$, a value in $(-\pi/2, \pi/2)$.
3. **Lead** ($a < b$). For $\omega > 0$ the phase is positive. It is largest at $\omega^* = \sqrt{ab}$, where

    $$\sin \varphi_{\max} = \frac{b - a}{b + a}, \qquad \tan \varphi_{\max} = \frac{b - a}{2\sqrt{ab}},$$

    so $\varphi_{\max} < \pi/2$. The phase increases on $(0, \sqrt{ab}]$ and decreases on $[\sqrt{ab}, \infty)$.

4. **Lag** ($a > b$). The same formulas hold with the signs reversed. The phase is negative for $\omega > 0$ and smallest at $\sqrt{ab}$, with $\sin \varphi_{\min} = -(a - b)/(a + b)$.

**Proof.**

- **Parts 1 and 2.** These follow from $C(i\omega) = k(a + i\omega)/(b + i\omega)$. Since $a, b > 0$, the factors $a + i\omega$ and $b + i\omega$ lie in the open right half-plane, so their arguments are $\arctan(\omega/a)$ and $\arctan(\omega/b)$.
- **Part 3.** For $\omega > 0$, $\tan \varphi(\omega) = \dfrac{\omega/a - \omega/b}{1 + \omega^2/(ab)} = \dfrac{(b - a)\,\omega}{ab + \omega^2}$.
    - The map $\omega \mapsto \omega/(ab + \omega^2)$ increases on $(0, \sqrt{ab}]$ and decreases afterwards, and $\tan$ is increasing on $(0, \pi/2)$, which gives the monotonicity and the maximizer.
    - At $\omega^*$, $\tan \varphi_{\max} = (b - a)/(2\sqrt{ab})$, and $\sin \varphi_{\max} = \tan \varphi_{\max} / \sqrt{1 + \tan^2 \varphi_{\max}} = (b - a)/(b + a)$, because $(2\sqrt{ab})^2 + (b - a)^2 = (a + b)^2$.
- **Part 4.** Exchange the roles of $a$ and $b$.

## Sources

- K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*, 2nd ed., Princeton University Press, 2021 (electronic edition v3.0i, <http://fbsbook.org>), Section 12.3, the lead and lag compensators $C(s) = k(s + a)/(s + b)$ of equation (12.7): lead for $a < b$ with phase lead between $\omega = a$ and $\omega = b$, lag for $a > b$, and Figure 12.9 (pp. 12-15–12-16). The location and value of the maximum phase lead are derived on the page.
