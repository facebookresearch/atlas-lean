# Shor's order-finding algorithm

Shor's algorithm finds the multiplicative order $r$ of $x$ modulo $n$. It prepares a uniform superposition over $a < q$, where $q$ is a power of two with $n^2 \le q < 2n^2$, computes $x^a \bmod n$ into a second register, applies the quantum Fourier transform on $q$ states and observes an integer $c$. With probability bounded below, $c/q$ lies within $1/(2q)$ of a fraction $d/r$. The classical post-processing recovers $d/r$ in lowest terms as a convergent of the continued fraction of $c/q$ (P. W. Shor, SIAM J. Comput. 26 (1997), Section 5). The statements below concern this post-processing step; the probability of a good outcome $c$ is bounded separately in Shor's equations (5.5)–(5.11).

- [Uniqueness of the fraction recovered in Shor's algorithm](eq-of-abs-sub-le-of-lt.md)
- [Continued fractions recover the fraction in Shor's algorithm](exists-convergent-eq-of-abs-sub-le.md)

## Related topics

- [Shor's reduction of factoring to order finding](../shor-s-reduction-of-factoring-to-order-finding/README.md): the order found here gives a factor of $n$ by the $\gcd(x^{r/2} - 1, n)$ step.
- [Continued fractions and expansions of reals](../../../NumberTheory/continued-fractions-expansions/README.md): the convergents that the post-processing searches.
- [Quantum Fourier transform](../../../QuantumInformation/quantum-operations/quantum-fourier-transform/README.md): the unitary $A_q$ applied before the measurement.
