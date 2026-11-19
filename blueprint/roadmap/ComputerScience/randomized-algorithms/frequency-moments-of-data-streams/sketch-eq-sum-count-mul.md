# The one-pass sketch is linear in the frequencies

Let $\iota$ be a finite set, $(\varepsilon_i)_{i \in \iota}$ real-valued functions on $\Omega$ and $l = (a_1, \dots, a_m)$ a stream over $\iota$, with $m_i$ the number of occurrences of $i$ in $l$. Then for every $\omega \in \Omega$,

$$\sum_{t=1}^{m} \varepsilon_{a_t}(\omega) = \sum_{i \in \iota} m_i\, \varepsilon_i(\omega),$$

so the sketch $Z = \sum_i \varepsilon_i m_i$ of Alon, Matias and Szegedy can be maintained with one addition per arriving element (N. Alon, Y. Matias and M. Szegedy, *J. Comput. System Sci.* 58 (1999), proof of Theorem 2.2: "Z is a linear function of the numbers $m_i$, and can thus be computed in one pass").

## Background

- [The AMS sketch of a stream](sketch.md): the quantity computed in one pass.
