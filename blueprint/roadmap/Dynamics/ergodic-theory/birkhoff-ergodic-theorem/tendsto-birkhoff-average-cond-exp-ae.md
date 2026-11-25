# Birkhoff's pointwise ergodic theorem

Let $\mu$ be a finite measure on $X$, $T : X \to X$ a measurable map preserving $\mu$, and $f : X \to \mathbb{R}$
an integrable function. Then for $\mu$-almost every $x$,

$$\frac{1}{n} \sum_{k=0}^{n-1} f(T^k x) \longrightarrow \mathbb{E}_\mu[f \mid \mathcal{I}](x) \qquad (n \to \infty),$$

where $\mathcal{I}$ is the σ-algebra of measurable sets $E$ with $T^{-1} E = E$. When $\mu$ is a probability measure
and $T$ is ergodic the limit is the constant $\int f \, d\mu$
([ergodic case](birkhoff-pointwise-ergodic.md), [Birkhoff limit of an ergodic map](birkhoff-limit-ae-eq-integral-of-ergodic.md)).

## Sources

- G. D. Birkhoff, *Proof of the ergodic theorem*, Proc. Natl. Acad. Sci. USA 17 (1931), 656–660.
