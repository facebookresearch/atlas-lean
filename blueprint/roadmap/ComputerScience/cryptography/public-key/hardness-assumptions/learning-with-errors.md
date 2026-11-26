# Decision learning-with-errors assumption

Let $m$ and $q$ be functions of the dimension $n$ bounded by polynomials in $n$, with $q(n) \ge 1$, and let $\chi_n$ be a probability distribution on $\mathbb{Z}_{q(n)}$ for every $n$. A distinguisher $D$ in dimension $n$ maps a matrix in $\mathbb{Z}_{q(n)}^{m(n) \times n}$, a vector in $\mathbb{Z}_{q(n)}^{m(n)}$ and coins in a finite nonempty set $S_n$ to a bit. Its decision LWE advantage is $|\Pr[D(A, As + e, c) = 1] - \Pr[D(A, u, c) = 1]|$, where $A \in \mathbb{Z}_{q(n)}^{m(n) \times n}$, $s \in \mathbb{Z}_{q(n)}^n$, $u \in \mathbb{Z}_{q(n)}^{m(n)}$ and the coins $c \in S_n$ are uniform and the error $e \in \mathbb{Z}_{q(n)}^{m(n)}$ is drawn from $\chi_n^{m(n)}$, all independently: the decision problem is to distinguish the LWE samples $(A, As + e)$ from uniform ones $(A, u)$. Fix a class of admissible distinguisher families, each giving one distinguisher $D_n$ for every $n$. The decision LWE assumption holds for these parameters and this class when every admissible family has negligible advantage $n \mapsto \mathrm{adv}(D_n)$.

In the sources the admissible families are those computed by one probabilistic algorithm running in time polynomial in $n$. The assumption holds vacuously when no family is admissible.

## Sources

- O. Regev, "On lattices, learning with errors, random linear codes, and cryptography", *Journal of the ACM* 56(6), Article 34, 2009, Section 1 (the samples as a matrix and a vector, with $m$ and the modulus polynomial in $n$) and Section 2 (negligible functions, distinguishers, and efficient algorithms as those running in time polynomial in $n$); <https://arxiv.org/abs/2401.03703>
- C. Peikert, "A decade of lattice cryptography", *Foundations and Trends in Theoretical Computer Science* 10(4):283–424, 2016, Section 4.2.1, Definitions 4.2.1 (the LWE distribution) and 4.2.3 (decision LWE); ePrint 2015/939, <https://eprint.iacr.org/2015/939>
