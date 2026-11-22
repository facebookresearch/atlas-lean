# Marginal density of a Gaussian location mixture

Let $g$ be a measure on $\mathbb R$, the prior of a location parameter $\mu$ (atoms are allowed), and let $v > 0$. The marginal density is

$$f(x) = \int \varphi_v(x - \mu)\, g(d\mu), \qquad \varphi_v(t) = (2\pi v)^{-1/2} e^{-t^2/(2v)} .$$

When $g$ is a probability measure, $f$ is the density of $x$ in the model $\mu \sim g$, $x \mid \mu \sim \mathcal N(\mu, v)$ (Efron 2011, equations (1.2)–(1.3), with $\sigma^2 = v$).

If $\mu \mapsto \varphi_v(x - \mu)$ is not $g$-integrable (possible only for an infinite measure $g$), the integral is read as $0$.

## Sources

- Bradley Efron, *Tweedie's formula and selection bias*, J. Amer. Statist. Assoc. 106 (2011), no. 496, 1602–1614, DOI 10.1198/jasa.2011.tm11181. Equation numbers are those of the author's manuscript at https://efron.ckirby.su.domains/papers/2011TweediesFormula.pdf.
