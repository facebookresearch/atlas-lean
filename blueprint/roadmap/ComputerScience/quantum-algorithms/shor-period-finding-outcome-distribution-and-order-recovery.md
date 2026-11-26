# Shor period finding: outcome distribution and order recovery

Let $N \ge 2$, let $x$ be a unit modulo $N$ of order $r$ (so $r < N$), and let $q = 2^L$ with
$N^2 \le q < 2N^2$. Apply the quantum Fourier transform modulo $q$ to the first register of
$q^{-1/2} \sum_{a=0}^{q-1} \lvert a \rangle \lvert x^a \bmod N \rangle$ and measure both registers,
obtaining $(c, x^k \bmod N)$ with $0 \le c < q$ and $0 \le k < r$. Call $c$ good for an integer $d$ if
$\lvert rc - dq \rvert \le r/2$, and good if it is good for some integer $d$. Then $c$ is good if and only if the
residue of $rc$ modulo $q$, taken in the centered range $(-q/2, q/2]$, lies in $[-r/2, r/2]$, and in that case the
integer $d$ is unique ($r/2 < q/2$), namely $d = (rc - \rho)/q$ for that centered residue $\rho$. For a fixed $d$ the
residue test is not equivalent to goodness for $d$: for $N = 7$, $r = 6$, $q = 64$, $c = 0$ and $d = 1$ the residue is
$0$ but $\lvert rc - dq \rvert = 64$. The test must also use the centered residue rather than the ordinary one: for
$c = 53$ the ordinary residue of $6 \cdot 53$ modulo $64$ is $62$, while $6 \cdot 53 - 5 \cdot 64 = -2$.

1. For $N$ sufficiently large, the probability that the measured $c$ is good for some $d$ with $\gcd(d, r) = 1$ is at
   least $\varphi(r)/(3r)$.
2. If $c$ is good for $d$ with $\gcd(d, r) = 1$, then $\lvert c/q - d/r \rvert \le 1/(2q)$, so $d/r$ in lowest terms is
   among the convergents of the continued-fraction expansion of $c/q$, and $r$ is its denominator.

Item 1 is asymptotic, as in the source; a version with an explicit constant and an explicit threshold on $N$ is a
separate page. Recovering a factor of $N$ from $r$ is a separate, downstream reduction.

## Depends on

- [Quantum Fourier transform matrix](../../QuantumInformation/quantum-operations/quantum-fourier-transform/qft-matrix.md)

## Proof depends on

- [Shor per-outcome probability bound (asymptotic source form)](shor-per-outcome-probability-bound.md)
- [Continued fractions recover the fraction in Shor's algorithm](shor-s-order-finding-algorithm/exists-convergent-eq-of-abs-sub-le.md)
- [Uniqueness of the fraction recovered in Shor's algorithm](shor-s-order-finding-algorithm/eq-of-abs-sub-le-of-lt.md)

## Sources

- P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum
  computer*, SIAM Journal on Computing 26 (1997); arXiv:quant-ph/9508027v2, Section 5, equations
  (5.11)–(5.13) and the surrounding text. <https://arxiv.org/abs/quant-ph/9508027>
- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6. <https://arxiv.org/abs/1907.09415v6> Background reference.
