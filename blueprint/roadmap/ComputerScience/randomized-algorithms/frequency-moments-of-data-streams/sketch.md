# The AMS sketch of a stream

Let $(\varepsilon_i)_{i \in \iota}$ be real-valued functions on a sample space $\Omega$. For a stream $l = (a_1, \dots, a_m)$ of elements of $\iota$ and $\omega \in \Omega$, the AMS sketch is

$$Z(\omega) = \sum_{t=1}^{m} \varepsilon_{a_t}(\omega),$$

accumulated in one pass by adding the value $\varepsilon_{a_t}(\omega)$ associated with each arriving element (a random sign $\pm 1$ in the AMS algorithm) (N. Alon, Y. Matias and M. Szegedy, *J. Comput. System Sci.* 58 (1999), proof of Theorem 2.2). It is $0$ for the empty stream.
