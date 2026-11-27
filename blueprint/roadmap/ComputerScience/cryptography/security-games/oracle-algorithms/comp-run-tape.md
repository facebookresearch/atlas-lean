# Postcomposition changes both exits of a tape run

Fix a deterministic algorithm $e : M \times \mathrm{Rnd} \to C$ (typically encryption with explicit randomness), a default value $d$ and a continuation $K$ that maps an output $a$, a length $n'$ and a tape $\rho' \in \mathrm{Rnd}^{n'}$ to a value. For every map $f$ on the values, oracle algorithm $c$, length $n$ and tape $\rho \in \mathrm{Rnd}^n$, writing $\mathrm{run}_{e, d, K}(c, n, \rho)$ for the [tape run](run-tape.md) with default $d$ and continuation $K$, applying $f$ to it gives the tape run with default $f(d)$ and continuation $(a, n', \rho') \mapsto f(K(a, n', \rho'))$:

$$f\big(\mathrm{run}_{e, d, K}(c, n, \rho)\big) = \mathrm{run}_{e,\ f(d),\ f \circ K}(c, n, \rho).$$

Both exits change: the default becomes $f(d)$ and the continuation becomes $f \circ K$ pointwise.
