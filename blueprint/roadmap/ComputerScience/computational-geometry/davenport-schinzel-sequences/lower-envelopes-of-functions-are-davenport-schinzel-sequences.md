# Lower envelopes of functions are Davenport–Schinzel sequences

Let $F = \{f_1, \dots, f_n\}$ be continuous real functions on a common interval $I \subseteq \mathbb{R}$, any two of which intersect in at most $s$ points. The *lower envelope* is $L_F(x) = \min_i f_i(x)$. Its *envelope sequence* $\varphi(F) = (\varphi_1, \dots, \varphi_\ell)$ is a shortest sequence of indices for which $I$ can be divided into consecutive intervals $I_1, \dots, I_\ell$, in this order, with $f_{\varphi_j} = L_F$ on all of $I_j$; the $f_{\varphi_j}$ are the *pieces* of the envelope. In a shortest sequence consecutive indices differ and, unless $I$ is a single point, every $I_j$ has positive length, so a function that touches the envelope only at isolated points without being below it starts no piece: for $f = 0$ and $g = x^2$ on $[-1, 1]$ the sequence is $(f)$, not $(f, g, f)$. Then $\varphi(F)$ is an $(n, s)$-Davenport–Schinzel sequence; in particular $\ell \le \lambda_s(n)$.

## Depends on

- [Davenport–Schinzel sequence](davenport-schinzel-sequence.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 12 (Davenport–Schinzel sequences), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%2012.pdf>: Observation 12.3 and the definition of the lower envelope sequence before it (maximal pieces on each of which a single function defines the envelope; the shortest-sequence form here fixes how ties are counted)
