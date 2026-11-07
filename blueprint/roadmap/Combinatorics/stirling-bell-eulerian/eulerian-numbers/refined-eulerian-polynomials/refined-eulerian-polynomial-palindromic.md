# Palindromicity of the refined Eulerian polynomials

Let $n \ge 1$. For a permutation
$\sigma$ of $\{1, \dots, n\}$, let $\mathrm{odes}(\sigma)$ (resp. $\mathrm{edes}(\sigma)$) be the
number of odd (resp. even) positions $i \in \{1, \dots, n-1\}$ with $\sigma(i) > \sigma(i+1)$,
and let $A_n(p, q) = \sum_{\sigma} p^{\mathrm{odes}(\sigma)} q^{\mathrm{edes}(\sigma)}$, the sum
over all permutations $\sigma$ of $\{1, \dots, n\}$, be the refined Eulerian polynomial with real
coefficients. Let $P_n = (1+q) A_n$ if $n$ is even and $P_n = A_n$ if $n$ is odd. Then $P_n$ is
palindromic of darga $\lfloor n/2 \rfloor$: it is a nonzero polynomial, $P_n(p, q) = P_n(q, p)$
for all real $p$ and $q$, and $P_n(p, q) = (pq)^{\lfloor n/2 \rfloor} P_n(1/p, 1/q)$ for all
nonzero real $p$ and $q$.

## Sources

- Hua Sun, "A New Class of Refined Eulerian Polynomials," Journal of Integer Sequences 21 (2018), Article 18.5.5, Theorem (label pal), lines 160–162 (polynomial definition lines 135–136, palindromic-darga definition lines 105–110). `https://cs.uwaterloo.ca/journals/JIS/VOL21/Sun/sun2.tex`
