# Concentration of tumour malignancy on a single trait under phenotype-structured immune pressure

**Model.** Tumour cells $n(t,x)$ carry a malignancy trait $x \in [0,1]$; effector lymphocytes (activated NK and competent T cells) $\ell(t,y)$ and naïve or inactive lymphocytes $p(t,y)$ carry an anti-tumour aggressiveness trait $y \in [0,1]$. Without treatment (or with a constant checkpoint-inhibitor dose absorbed into $\nu$), in the innate, non-adaptive case

$$
\begin{aligned}
\partial_t n(t,x) &= \big[r(x) - d(x)\rho(t) - \mu(x)\varphi(t)\big]\, n(t,x),\\
\partial_t \ell(t,y) &= p(t,y) - \big(\nu(y)\rho(t) + k_1\big)\,\ell(t,y),\\
\partial_t p(t,y) &= \chi(t,y)\,p(t,y) - k_2\, p(t,y)^2,
\end{aligned}
$$

with tumour mass $\rho(t) = \int_0^1 n(t,x)\,dx$, immune pressure $\varphi(t) = \int_0^1 \psi(y)\ell(t,y)\,dy$, and stimulation $\chi(t,y) = \int_0^1 \omega(x,y) n(t,x)\,dx$. Here $r$ is the proliferation rate, $d\rho$ nonlocal competition, $\mu$ susceptibility to immune killing, $\nu$ immunoediting (exhaustion of effectors by the tumour) and $k_1, k_2 > 0$ decay and self-limitation rates.

**Hypotheses.** The functions $r, d, \mu, \psi, \nu$ are positive and continuous on $[0,1]$, $\omega$ is positive and continuous on $[0,1]^2$, the initial data are continuous with $n^0 > 0$ and $p^0 > 0$ on $[0,1]$, and for all $0 < \rho \le \bar\rho$, $0 < \varphi \le \bar\varphi$ (a priori bounds on the long-time mass and pressure) the fitness $x \mapsto r(x) - d(x)\rho - \mu(x)\varphi$ has a unique maximizer $x(\rho,\varphi)$; strict concavity of this function suffices.

**Theorem.** Suppose $n(t,\cdot)$ converges weakly in the space of measures on $[0,1]$ to $n^\infty$. Then either $n^\infty = 0$ (eradication) or

$$
n^\infty = \rho^\infty\, \delta_{x^\infty}, \qquad x^\infty = x(\rho^\infty, \varphi^\infty),
$$

where $(\rho^\infty, \varphi^\infty)$ solves

$$
\rho = \max_{x \in [0,1]} \frac{r(x) - \mu(x)\varphi}{d(x)}, \qquad \varphi = \frac{\rho}{k_2}\int_0^1 \frac{\psi(y)\,\omega(x(\rho,\varphi), y)}{\nu(y)\rho + k_1}\,dy.
$$

The lymphocyte densities then converge pointwise to $p^\infty(y) = \frac{1}{k_2}\int_0^1 \omega(x,y)\,dn^\infty(x)$ and $\ell^\infty(y) = p^\infty(y)/(\nu(y)\rho^\infty + k_1)$. If moreover $\min_{x}\big(r(x) - \mu(x)\bar\varphi\big) > 0$, the tumour mass stays bounded away from zero, eradication is impossible and the Dirac limit is the only option.

In the adaptive case, where the pressure is trait-specific, $\varphi(t,x) = \int_0^1 \Psi(x,y)\ell(t,y)\,dy$, the same dichotomy holds with $x^\infty$ the unique maximizer of $r(x) - d(x)\rho - \mu(x)\int_0^1 \Psi(x,y)\ell(y)\,dy$ and a fixed-point system in $(\rho, \ell) \in \mathbb{R} \times C([0,1])$.

## Expansion

The equations for $p$ and $\ell$ are logistic and linear in their own variables, giving $\limsup_t p \le \omega^M(y)\rho^\star/k_2$, $\limsup_t \ell \le \bar p/k_1$ and hence $\limsup_t \varphi \le \bar\varphi$; dominated convergence then turns the weak convergence of $n$ into convergence of $\varphi$, $\ell$ and $p$. For each fixed $x$, $n(t,x)$ solves $z' = a(t)z$ with $a(t) \to r(x) - d(x)\rho^\infty - \mu(x)\varphi^\infty$. If this limit fitness were positive at some $x_0$, positivity of $n^0$ on an interval around $x_0$ would make $\rho$ grow exponentially, contradicting convergence; if it were negative everywhere, $\rho \to 0$. So the limit fitness has maximum exactly $0$, which is the equation for $\rho^\infty$, and the limit measure must sit on the zero set, which the unique-maximizer hypothesis reduces to the single trait $x^\infty$. This is the standard selection mechanism of phenotype-structured models without mutation: the population concentrates on the fittest trait in the environment it creates.

## Proof depends on

- [Dominated convergence theorem for nonnegative functions](../../../../../MeasureTheory/integration/dominated-convergence-theorem/tendsto-lintegral-of-dominated-convergence.md)

## Sources

- Z. Kaid, C. Pouchol and J. Clairambault, *A phenotype-structured model for the tumour-immune response*, arXiv:2301.05473 (2023), Section 3.4 (model), Section 4.1 (a priori bounds, Lemma 1, Theorem 4.1, Remarks 4.1–4.2) and Section 4.1.4 (Theorem 4.2). <https://doi.org/10.48550/arXiv.2301.05473>
