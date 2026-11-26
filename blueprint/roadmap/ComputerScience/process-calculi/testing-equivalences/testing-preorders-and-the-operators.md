# Testing preorders are preserved by parallel composition but not by choice

In the calculus of [may and must testing](may-and-must-testing-preorders.md):

1. each of $\sqsubseteq_{\mathrm{may}}$, $\sqsubseteq_{\mathrm{must}}$ and $\sqsubseteq_{\mathrm{test}}$ is preserved by parallel composition: $p \sqsubseteq q$ implies $p \mid r \sqsubseteq q \mid r$ for every closed $r$;
2. $\sqsubseteq_{\mathrm{must}}$ and $\sqsubseteq_{\mathrm{test}}$ are not preserved by choice: $\alpha \sqsubseteq_{\mathrm{must}} \tau\alpha$, but $\lambda + \alpha \not\sqsubseteq_{\mathrm{must}} \lambda + \tau\alpha$ for visible actions $\lambda \ne \alpha$, since $\lambda + \alpha$ must satisfy the observer $\bar\lambda\omega$ while $(\lambda + \tau\alpha) \mid \bar\lambda\omega$ can move silently to the deadlocked term $\alpha \mid \bar\lambda\omega$.

## Depends on

- [May and must testing preorders](may-and-must-testing-preorders.md)

## Sources

- R. De Nicola and M. C. B. Hennessy, "Testing equivalences for processes", *Theoretical Computer Science* 34(1–2):83–133, 1984, <https://www.scss.tcd.ie/Matthew.Hennessy/pubs/old/TCS84.pdf>, Section 2.2: Proposition 2.2.1 (preservation by $\mid$, proved by moving $r$ into the observer) and the counterexample for $+$ that follows it, which motivates the precongruences of Definition 2.2.2.
