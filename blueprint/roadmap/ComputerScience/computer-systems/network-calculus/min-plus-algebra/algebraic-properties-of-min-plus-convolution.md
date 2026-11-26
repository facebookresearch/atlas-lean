# Algebraic properties of min-plus convolution

For $f, g, h$ in the set $\mathcal F$ of [min-plus convolution](min-plus-convolution-and-deconvolution.md):

1. (closure) $f \otimes g \in \mathcal F$;
2. (associativity) $(f \otimes g) \otimes h = f \otimes (g \otimes h)$;
3. (absorbing zero) with $\varepsilon(t) = +\infty$ for $t \ge 0$ and $\varepsilon(t) = 0$ for $t < 0$, $f \otimes \varepsilon = \varepsilon$;
4. (neutral element) with $\delta_0(t) = +\infty$ for $t > 0$ and $\delta_0(t) = 0$ for $t \le 0$, $f \otimes \delta_0 = f$;
5. (commutativity) $f \otimes g = g \otimes f$;
6. (distributivity) $(f \wedge g) \otimes h = (f \otimes h) \wedge (g \otimes h)$, where $\wedge$ is the pointwise minimum;
7. (constants) $(f + K) \otimes g = (f \otimes g) + K$ for every constant $K \ge 0$;
8. (isotonicity) if $f \le g$ and $f' \le g'$, then $f \otimes f' \le g \otimes g'$.

Rules 1–6 make $(\mathcal F, \wedge, \otimes)$ a commutative dioid.

## Depends on

- [Min-plus convolution and deconvolution](min-plus-convolution-and-deconvolution.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 3.1.6, Theorem 3.1.5 (Rules 1–7, with the proof of Rules 1 and 2) and Theorem 3.1.7 (Rule 10, isotonicity).
