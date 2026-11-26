# Binary relative entropy

For $q, p \in [0,1]$ the *binary relative entropy* (Kullback-Leibler divergence between Bernoulli distributions), in nats, is

$$
\mathrm{kl}(q \,\|\, p) = q \ln\frac{q}{p} + (1-q)\ln\frac{1-q}{1-p},
$$

with the conventions $0 \ln(0/a) = 0$ and $a\ln(a/0) = +\infty$ for $a > 0$. It is finite whenever $p \in (0,1)$, or $p \in \{0,1\}$ and $q = p$; it is nonnegative, vanishes exactly when $q = p$, and for fixed $p \in [0,1]$ the map $q \mapsto \mathrm{kl}(q\,\|\,p)$ is convex on $[0,1]$ (as is $q \mapsto e^{t\,\mathrm{kl}(q\|p)}$ for $t \ge 0$).

## Depends on

- [Kullback–Leibler divergence of finite probability laws](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-to-measure.md)

## Sources

- T. M. Cover and J. A. Thomas, "Elements of Information Theory", Wiley-Interscience, 2nd ed., 2006.
