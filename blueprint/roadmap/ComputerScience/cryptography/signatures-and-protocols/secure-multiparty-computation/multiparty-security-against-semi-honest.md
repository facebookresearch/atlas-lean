# Multiparty security against semi-honest adversaries

Let $f : X_1 \times \cdots \times X_n \to Y_1 \times \cdots \times Y_n$ be a deterministic $n$-party functionality and $\pi$ a protocol. For a set $I$ of parties, $\mathrm{view}^\pi_I(x)$ is the joint view (inputs, randomness and received messages) of $I$ in an execution on input $x$ and $\mathrm{output}^\pi(x)$ the parties' outputs. The protocol $t$-privately computes $f$ if $\mathrm{output}^\pi(x) = f(x)$ and for every $I$ with $|I| \le t$ there is a simulator $S_I$ such that for every input vector $x$,

$$\bigl(S_I(x_I, f_I(x)),\ f(x)\bigr) \quad\text{and}\quad \bigl(\mathrm{view}^\pi_I(x),\ \mathrm{output}^\pi(x)\bigr)$$

are identically distributed (perfect privacy), statistically close, or computationally indistinguishable with an efficient $S_I$, where $x_I$ and $f_I(x)$ are the inputs and outputs of the parties in $I$.

In the computational variant, the functionality, the protocol and the inputs are indexed by a security parameter $\lambda$, each $S_I$ runs in time polynomial in $\lambda$, and indistinguishability is as $\lambda \to \infty$ uniformly over input vectors of polynomial length.

## Depends on

- [Efficient adversaries](../../security-games/asymptotic-security/efficient-adversaries.md)
- [Winning probability of a game](../../security-games/games-and-advantages/win-prob.md)

## Sources

- G. Asharov and Y. Lindell, "A full proof of the BGW protocol for perfectly secure multiparty computation", *Journal of Cryptology* 30(1):58–151, 2017; ePrint 2011/136, <https://eprint.iacr.org/2011/136>
- Y. Lindell, "How to simulate it: a tutorial on the simulation proof technique", in *Tutorials on the Foundations of Cryptography*, Springer, 2017; ePrint 2016/046, <https://eprint.iacr.org/2016/046>
