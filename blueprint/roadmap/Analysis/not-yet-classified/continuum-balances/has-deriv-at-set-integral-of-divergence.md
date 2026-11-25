# Integral balance in divergence form

Let $\Omega \subseteq \mathbb R^n$ be compact with Lebesgue measure, let the density $u(t, x)$ be jointly $C^1$, let $q(t, \cdot)$ be a flux field with divergence $\operatorname{div} q = \sum_i \partial_i q_i$, and let $s(t, \cdot)$ be integrable on $\Omega$. Suppose at time $t$ the local law $\partial_t u + \operatorname{div} q = s$ holds on $\Omega$, and suppose the divergence theorem holds in the form $\int_\Omega \operatorname{div} q(t, x)\,dx = \Phi(t)$, where $\Phi(t)$ is the outward boundary flux; this identity is a hypothesis. Then

$$\frac{d}{dt} \int_\Omega u(t, x)\,dx = -\Phi(t) + \int_\Omega s(t, x)\,dx.$$

For $\Omega = [a, b]$ with $a \le b$, the outward flux is $q(t, b) - q(t, a)$.
