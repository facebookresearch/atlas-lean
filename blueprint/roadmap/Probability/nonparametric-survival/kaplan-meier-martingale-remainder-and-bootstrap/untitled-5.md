# History filtration of the exponential censoring model

In the exponential censoring model the sample space is $\mathbb R$ with its Borel $\sigma$-algebra, the failure time is $T(\omega) = \omega$ and the censoring time is $C(\omega) = 1$. The observed failure and censoring counting processes are

$$N(u)(\omega) = \mathbf 1\{T(\omega) \le C(\omega),\ T(\omega) \le u\}, \qquad N^c(u)(\omega) = \mathbf 1\{C(\omega) < T(\omega),\ C(\omega) \le u\}.$$

The history filtration $(\mathcal F_t)_{t \in \mathbb R}$ is the natural filtration of the observed process $u \mapsto (N(u), N^c(u))$:

$$\mathcal F_t = \sigma\bigl(N(u), N^c(u) : u \le t\bigr),$$

the smallest $\sigma$-algebra making every pair $(N(u), N^c(u))$ with $u \le t$ measurable into $\mathbb R^2$ with its Borel $\sigma$-algebra.
