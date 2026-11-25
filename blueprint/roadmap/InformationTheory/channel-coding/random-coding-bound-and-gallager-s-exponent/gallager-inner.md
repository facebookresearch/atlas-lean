# Gallager's inner sum

Let $W$ be a discrete memoryless channel with finite input alphabet $\mathcal A$ and finite output
alphabet $\mathcal B$, given by its transition laws $W(\cdot \mid a)$, and let $p$ be a law on
$\mathcal A$. For a real $\rho$ and an output $b$, Gallager's inner sum is

$$g_b(\rho) = \sum_{a \in \mathcal A} p(a)\, W(b \mid a)^{1/(1+\rho)},$$

the quantity raised to the power $1 + \rho$ in [Gallager's function](gallager-e0.md). The power is the
real power $x^y$ with $0^y = 0$ for $y \ne 0$, so for $\rho > -1$ an input that cannot produce $b$
contributes $0$.

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, equation (20).
