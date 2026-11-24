# Relative entropy of measures

Let $\mu$ and $\nu$ be measures on a measurable space $\Omega$. The relative entropy, or Kullback–Leibler
divergence, of $\mu$ with respect to $\nu$ is the element of $[0, \infty]$

$$
D(\mu \,\|\, \nu) =
\begin{cases}
\max\Big(0,\ \displaystyle\int_\Omega \log \frac{d\mu}{d\nu} \, d\mu + \nu(\Omega) - \mu(\Omega)\Big)
  & \text{if } \mu \ll \nu \text{ and } \log \frac{d\mu}{d\nu} \text{ is } \mu\text{-integrable}, \\
\infty & \text{otherwise.}
\end{cases}
$$

Here $\log \frac{d\mu}{d\nu}$ is the log-likelihood ratio: the natural logarithm of the Radon–Nikodym derivative
$\frac{d\mu}{d\nu}$, taken as a real number (an infinite value counts as $0$), with $\log 0 = 0$. A total mass
$\mu(\Omega)$ or $\nu(\Omega)$ that is infinite counts as $0$. The derivative is the density $f$ of a Lebesgue
decomposition $\mu = \xi + f \cdot \nu$ with $\xi$ singular with respect to $\nu$, one such $f$ being chosen when a
decomposition exists, and the zero function when none exists; in the latter case the log-likelihood ratio is $0$.
So the log-likelihood ratio is a real function, its integral is the integral of a real function, and the expression
inside the maximum is a real number; its maximum with $0$ is a finite element of $[0, \infty]$.

For probability measures both masses are $1$, and the definition reads
$D(\mu \,\|\, \nu) = \max\big(0, \int_\Omega \log \frac{d\mu}{d\nu} \, d\mu\big)$ if $\mu \ll \nu$ and the
log-likelihood ratio is $\mu$-integrable, and $D(\mu \,\|\, \nu) = \infty$ otherwise.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy,
  <https://tor-lattimore.com/downloads/book/book.pdf>), Section 14.2: definition (14.5) and Theorem 14.1, the
  relative entropy of probability measures on an arbitrary measurable space.
