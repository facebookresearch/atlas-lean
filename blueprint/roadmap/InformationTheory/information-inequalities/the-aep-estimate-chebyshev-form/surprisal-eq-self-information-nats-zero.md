# Surprisal eq self Information Nats Zero Extension

Let $p$ be a probability mass function on a set $\alpha$ and let $a$ be in its support, $p(a) > 0$. The surprisal of $p(a)$ in bits, the value $-\log_2 p(a)$ in $[0, \infty]$ (which is $\infty$ for an outcome of probability $0$), equals

$$-\log_2 p(a) = \frac{I_p(a)}{\log 2},$$

where $I_p(a)$ is the self-information in nats, equal to $-\log p(a)$ when $p(a) > 0$ and to $0$ when $p(a) = 0$. The support hypothesis is needed: at an impossible outcome the surprisal is $\infty$ while $I_p(a) = 0$.
