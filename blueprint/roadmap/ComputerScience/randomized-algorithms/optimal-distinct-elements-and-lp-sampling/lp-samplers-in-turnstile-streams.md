# Approximate and perfect Lp samplers for turnstile streams

Let $p \ge 0$, $0 < \varepsilon < 1$, $0 < \delta < 1$ and $c > 0$. An *$(\varepsilon, \delta)$-approximate $L_p$ sampler* is a streaming algorithm on turnstile streams over $[n]$ that, at the end of any stream with final vector $x \ne 0$, fails (outputs a failure symbol) with probability at most $\delta$ and otherwise outputs an index $i \in [n]$ such that for every $j \in [n]$

$$
\Pr[\,i = j\,] = (1 \pm \varepsilon)\frac{|x_j|^p}{\|x\|_p^p} \pm n^{-c},
$$

with the convention $|x_j|^0 = \mathbf{1}[x_j \ne 0]$, so that an $L_0$ sampler returns an approximately uniform element of the support of $x$. It has *zero relative error* if the bound holds with $\varepsilon = 0$; samplers that also return the value $x_i$ are used for graph sketching.

## Depends on

- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)

## Sources

- Morteza Monemizadeh, David P. Woodruff, "1-Pass Relative-Error Lp-Sampling with Applications", SODA (2010).
- Hossein Jowhari, Mert Sağlam, Gábor Tardos, "Tight Bounds for Lp Samplers, Finding Duplicates in Streams, and Related Problems", PODS (2011), arXiv:1012.4889.
