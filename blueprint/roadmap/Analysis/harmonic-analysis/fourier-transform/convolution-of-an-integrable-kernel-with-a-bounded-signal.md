# Convolution of an integrable kernel with a bounded signal

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and $F$ a Banach space over $\mathbb{K}$. Let $h : \mathbb{R} \to \mathbb{K}$ be Lebesgue integrable, with $\|h\|_1 = \int |h|$, and let $u : \mathbb{R} \to F$ be strongly measurable with $\|u(t)\| \le K$ for almost every $t$. Then:

1. **Defined everywhere and bounded.** For every $t \in \mathbb{R}$ the Bochner integral $(h * u)(t) = \int_{\mathbb{R}} h(\tau)\, u(t - \tau)\, d\tau$ exists, and $\|(h * u)(t)\| \le \|h\|_1 K$.
2. **Continuous.** $h * u$ is uniformly continuous on $\mathbb{R}$.
3. **Independent of representatives.** If $h = h'$ and $u = u'$ almost everywhere, then $(h * u)(t) = (h' * u')(t)$ for every $t$. So $h * u$ is a well-defined continuous function of the classes of $h$ in $L^1$ and of $u$ in $L^\infty$.
4. **Linear and time invariant.** $u \mapsto h * u$ is linear, and $h * u(\cdot - s) = (h * u)(\cdot - s)$ for every $s \in \mathbb{R}$.
5. **Causal kernels.** If $h = 0$ almost everywhere on $(-\infty, 0)$, then $(h * u)(t)$ depends only on the values of $u$ on $(-\infty, t]$: if $u = u'$ almost everywhere on $(-\infty, t]$, then $(h * u)(t) = (h * u')(t)$.

In particular the system $u \mapsto h * u$ is bounded-input bounded-output stable with gain at most $\|h\|_1$.

**Proof.** For fixed $t$, the map $\tau \mapsto h(\tau) u(t - \tau)$ is strongly measurable and bounded in norm by $K|h(\tau)|$ for almost every $\tau$, because $\tau \mapsto t - \tau$ maps null sets to null sets; so it is Bochner integrable and part 1 follows. Writing $(h * u)(t) = \int h(t - \sigma) u(\sigma)\, d\sigma$, for $s, t \in \mathbb{R}$

$$\|(h * u)(t) - (h * u)(s)\| \le K \int |h(t - \sigma) - h(s - \sigma)|\, d\sigma = K\, \|h(\cdot + (t - s)) - h\|_1,$$

which tends to $0$ as $t - s \to 0$ by continuity of translation in $L^1(\mathbb{R})$; this is part 2. Changing $h$ or $u$ on a null set changes the integrand only on a null set, which gives part 3. Part 4 is linearity of the integral and the identity $\int h(\tau)\, u(t - s - \tau)\, d\tau = (h * u)(t - s)$. For part 5, the integral reduces to $\int_0^\infty h(\tau) u(t - \tau)\, d\tau$, which only involves $u$ on $(-\infty, t]$.

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014 (free version v1.1), <https://fourierandwavelets.org/FSP_v1.1_2014.pdf>, Section 4.3, Theorem 4.8 (BIBO stability, p. 357): a linear shift-invariant continuous-time system is BIBO-stable if and only if its impulse response is absolutely integrable. Existence at every time, continuity, independence of representatives and the causality clause for Banach-valued signals are derived on the page.
