# Linear parent–offspring regression model

Let $\mu$ be a probability measure on a measurable space $\Omega$ (the population). A linear parent–offspring model consists of real numbers $m$ (the population mean) and $h^2$ (the heritability, the regression slope) and real functions $P$ (the parental, or mid-parent, value) and $O$ (the offspring value) on $\Omega$ such that

- $P$ is measurable and $\mu$-integrable, and $O$ is $\mu$-integrable;
- $\int P \, d\mu = m$;
- the conditional expectation of $O$ given $\sigma(P)$ equals $m + h^2 (P - m)$ $\mu$-almost everywhere.

Equivalently $O = m + h^2 (P - m) + e$ with the conditional expectation of $e$ given $P$ equal to $0$. The biological heritability lies in $[0, 1]$, but no such condition is imposed.
