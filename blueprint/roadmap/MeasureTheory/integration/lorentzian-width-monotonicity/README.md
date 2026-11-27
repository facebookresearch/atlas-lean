# Monotonicity of Lorentzian integrals in the width

Let $\mu$ be a finite measure on $\mathbb{R}$, possibly zero, and $0 < \Gamma_1 \le \Gamma_2$. Then

$$\int \frac{\Gamma_1^2}{E^2 + \Gamma_1^2}\, d\mu(E) \le \int \frac{\Gamma_2^2}{E^2 + \Gamma_2^2}\, d\mu(E).$$

## Idea

The kernel $\Gamma^2 / (E^2 + \Gamma^2)$ is a Lorentzian line shape of width $\Gamma$, normalised
to the value $1$ at $E = 0$. For fixed $E \ne 0$ it equals $1 / (1 + E^2/\Gamma^2)$, which
increases strictly with $\Gamma$, while at $E = 0$ it is $1$ for every width. Integrating against
$\mu$ gives the monotonicity. When $\Gamma_1 < \Gamma_2$ the inequality is strict exactly when
$\mu(\mathbb{R} \setminus \{0\}) > 0$, that is, when $\mu$ has mass away from the origin.

## Statements

- [Lorentzian integrals are nondecreasing in the width](integral-lorentzian-mono.md)
- [Strict width monotonicity of Lorentzian integrals](integral-lorentzian-lt-iff.md): the strict form.
