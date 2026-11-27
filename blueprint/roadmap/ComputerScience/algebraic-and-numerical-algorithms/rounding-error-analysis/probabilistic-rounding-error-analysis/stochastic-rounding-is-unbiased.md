# Stochastic rounding is unbiased

For every real $x$ in the range of the floating-point numbers, the value $\mathrm{fl}(x)$ produced by [stochastic rounding](stochastic-rounding.md) satisfies $\mathbb{E}[\mathrm{fl}(x)] = x$; so for $x \ne 0$ the relative error $\delta = (\mathrm{fl}(x) - x)/x$ has mean zero. For $x \notin F$, rounding up or down with probability $1/2$ each gives $\mathbb{E}[\mathrm{fl}(x)] = (\lceil x \rceil + \lfloor x \rfloor)/2$ instead, which is not $x$ in general.

## Depends on

- [Stochastic rounding](stochastic-rounding.md)

## Sources

- M. P. Connolly, N. J. Higham and T. Mary, "Stochastic rounding and its probabilistic backward error analysis", *SIAM J. Sci. Comput.* 43(1):A566–A585, 2021; MIMS EPrint 2020.12, Section 4.1, Lemma 4.4 and its proof, and the remark after it on mode 1. <https://eprints.maths.manchester.ac.uk/2763/1/paper.pdf>
