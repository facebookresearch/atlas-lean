# Signature of a piecewise-linear path

Let $\tau_0 \le \tau_1 \le \tau_2 \le \cdots$ be reals and let the velocity of $X$ equal the
constant vector $x_j$ on each piece $(\tau_j, \tau_{j+1}]$, so that $X$ is linear on
$[\tau_j, \tau_{j+1}]$ with increment $\Delta_j = (\tau_{j+1} - \tau_j)\, x_j$. If the velocity is
interval integrable on every interval, then for every $n$

$$S(X)_{\tau_0, \tau_n} = \exp(\Delta_0) \otimes \exp(\Delta_1) \otimes \cdots \otimes \exp(\Delta_{n-1}),$$

the product taken left to right (an empty product is the unit series $1$). This is how
signatures of sampled data streams are computed in practice: no integral needs to be evaluated.

The source states it for the unit grid $\tau_j = j$; the proof, induction on $n$ with
[Chen's identity, algebraic form](signature-eq-tensor-mul.md) and
[the signature of a linear segment](signature-of-eq-on-ioc.md), is the same for any grid.

## Sources

- I. Chevyrev and A. Kormilitzin, *A primer on the signature method in machine learning*,
  arXiv:1603.03788v2, Corollary 1.23 (and Example 1.18 for a worked two-piece case).
