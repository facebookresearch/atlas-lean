# Approximate and perfect Lp samplers for turnstile streams

Let $p \ge 0$, $0 < \varepsilon < 1$, $0 < \delta < 1$ and $c > 0$. An *$(\varepsilon, \delta)$-approximate $L_p$ sampler* is a streaming algorithm on turnstile streams over $[n]$ that, at the end of any stream with final vector $x \ne 0$, fails (outputs a failure symbol) with probability at most $\delta$ and otherwise outputs an index $i \in [n]$ such that for every $j \in [n]$

$$
\Pr[\,i = j\,] = (1 \pm \varepsilon)\,\pi_p(x)_j \pm n^{-c}, \qquad \pi_p(x)_j = \frac{|x_j|^p}{\sum_{k \in [n]} |x_k|^p} \ (p > 0), \qquad \pi_0(x)_j = \frac{\mathbf{1}[j \in \mathrm{supp}\, x]}{|\mathrm{supp}\, x|},
$$

so that an $L_0$ sampler returns an approximately uniform element of the support $\mathrm{supp}\, x = \{k : x_k \ne 0\}$. (The $p = 0$ target cannot be written as $|x_j|^0/\|x\|_0^0$: with the convention $|x_j|^0 = \mathbf{1}[x_j \ne 0]$ the numerator is right, but $\|x\|_0 = |\mathrm{supp}\, x|$ gives $\|x\|_0^0 = 1$, which would assign probability near $1$ to each element of a two-element support.) It has *zero relative error* if the bound holds with $\varepsilon = 0$; samplers that also return the value $x_i$ are used for graph sketching.

## Depends on

- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)

## Sources

- Morteza Monemizadeh, David P. Woodruff, "1-Pass Relative-Error Lp-Sampling with Applications", SODA (2010).
- Hossein Jowhari, Mert Sağlam, Gábor Tardos, "Tight Bounds for Lp Samplers, Finding Duplicates in Streams, and Related Problems", PODS (2011), arXiv:1012.4889.
