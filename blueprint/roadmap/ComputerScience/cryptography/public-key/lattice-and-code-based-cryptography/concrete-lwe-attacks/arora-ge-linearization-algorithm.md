# Arora–Ge linearization algorithm for LWE with small error

For prime $q$ polynomial in $n$, Gaussian LWE error of standard deviation $\Theta(n^{\varepsilon})$ with $0<\varepsilon<1/2$, and $q\gg(n^{\varepsilon}\log n)^2$, the LWE secret can be learned with high probability in time $2^{\tilde O(n^{2\varepsilon})}$ by writing a polynomial that vanishes on all likely errors and linearizing it.

Let $q$ be a prime bounded by a polynomial in $n$ and $u\in\mathrm{GF}(q)^n$ unknown. The oracle $Q(u,\Psi)$ returns $(a,\,b=a\cdot u+\eta)$ with $a$ uniform in $\mathrm{GF}(q)^n$ and $\eta$ independent, obtained by drawing a real number from a centred normal distribution of standard deviation $\sigma$, rounding it to the nearest integer and reducing modulo $q$, with $\eta$ represented in $[-(q-1)/2,(q-1)/2]$. Arora and Ge write $\sigma=\alpha q$; their displayed density for this normal is normalised differently from their prose, which changes $\sigma$ by a constant factor and does not affect the statement below, stated for $\sigma=\Theta(n^{\varepsilon})$.

**Theorem.** If $\sigma=\Theta(n^{\varepsilon})$ for a constant $0<\varepsilon<1/2$ and $q\gg(\sigma\log n)^2$, there is an algorithm that runs in time $2^{\tilde O(n^{2\varepsilon})}$ and, with probability $1-o(1)$ over the samples and its coins, outputs $u$, given access to $Q(u,\Psi)$.

**Algorithm.** Fix $d$ with $2d+1<q$. The *truncated* oracle $Q(u,\Psi,d)$ draws $\eta$ from the same law conditioned on $|\eta|\le d$. The degree-$D=2d+1$ polynomial

$$
P(\eta)=\eta\prod_{i=1}^{d}(\eta+i)(\eta-i)
$$

vanishes on $[-d,d]$, so for every truncated sample the equation $P(b-a\cdot z)=0$ in unknowns $z\in\mathrm{GF}(q)^n$ holds at $z=u$. Replace each monomial $\prod_iz_i^{v_i}$ of degree $1\le\sum_iv_i\le D$ by a variable $y_v$ and add the constant coordinate $y_0=1$; the vector $y$ has $N=\binom{n+D}{D}$ coordinates, $N-1$ of them unknown. From $CN\sigma q\log q$ truncated samples, for a sufficiently large constant $C$ (Arora and Ge write $CN\alpha q^2\log q$ with $\sigma=\alpha q$), with high probability every solution of the resulting linear system has $y_{e_i}=u_i$ for all $i$, and Gaussian elimination recovers $u$.

## Expansion

Correctness for the truncated oracle (Theorem 3.3): the intended assignment satisfies every constraint. For a wrong assignment, Arora and Ge show that a random constraint is violated with probability $\Omega(1/(\sigma q))$: with probability $\Omega(1/\sigma)$ the noise is $0$ (Lemma 3.2, valid since $\sigma\ge1$ for $\varepsilon>0$), and then by the Schwartz–Zippel lemma, since $D<q$, the resulting nonzero polynomial in $a$ is nonzero with probability at least $1/q$. Hence a fixed wrong assignment satisfies all $CN\sigma q\log q$ independent constraints with probability at most $q^{-2N}$ for $C$ large enough, and a union bound over the at most $q^{N}$ wrong assignments gives success with high probability.

Truncation for the true oracle: for a centred normal $r$ of standard deviation $\sigma$, $\Pr[|r|>k\sigma]\le2e^{-k^2/2}$. Take $k=9\sigma\ln n$ and $d=\lceil k\sigma\rceil+1$; if $|r|\le k\sigma$ then the rounded value has absolute value at most $d<q/2$, so $|\eta|\le d$. Then $D=2d+1\le18\sigma^2\ln n+5$, which is at most $n$ for large $n$ because $\sigma^2\ln n=O(n^{2\varepsilon}\ln n)$ and $\varepsilon<1/2$; so $\ln N\le D\ln(n+D)\le 2D\ln n$. With $M=CN\sigma q\log q$ samples and $q$ polynomial in $n$, $\ln M\le 2D\ln n+O(\ln n)\le36\sigma^2\ln^2n+O(\ln n)$, while $k^2/2=40.5\,\sigma^2\ln^2n$. Thus all $M$ samples satisfy $|\eta|\le d$ except with probability at most $2Me^{-k^2/2}\le\exp(-4.5\,\sigma^2\ln^2n+O(\ln n))=o(1)$, and on that event they are distributed exactly as $M$ samples of the truncated oracle. The hypothesis $q\gg(\sigma\log n)^2$ ensures $2d+1<q$. Finally $N\le(n+D)^D=2^{\tilde O(n^{2\varepsilon})}$, so Gaussian elimination on $M$ constraints in $N-1$ unknowns runs in time $2^{\tilde O(n^{2\varepsilon})}$. The proof uses the Gaussian tail bound and the Schwartz–Zippel lemma. Sign convention: the source writes the substitution as $a\cdot z+b$; with $b=a\cdot u+\eta$ the consistent form is $b-a\cdot z$, used here. The error regime $\sigma\ge\sqrt n$ of Regev's reduction is outside the theorem.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Proof depends on

None.

## Sources

- Sanjeev Arora, Rong Ge, "New Algorithms for Learning in Presence of Errors", ICALP 2011, Lecture Notes in Computer Science 6755, pp. 403–415, https://doi.org/10.1007/978-3-642-22006-7_34; numbers from the author version ECCC TR10-066 revision 1, [https://eccc.weizmann.ac.il/report/2010/066/](https://eccc.weizmann.ac.il/report/2010/066/), Section 3: Theorem 3.1, Lemma 3.2, Equation (9) and Theorem 3.3.
- Martin Albrecht, Melissa Chase, Hao Chen, Jintai Ding, Shafi Goldwasser, Sergey Gorbunov, Shai Halevi, Jeffrey Hoffstein, Kim Laine, Kristin Lauter, Satya Lokam, Daniele Micciancio, Dustin Moody, Travis Morrison, Amit Sahai, Vinod Vaikuntanathan, "Homomorphic Encryption Standard", in Protecting Privacy through Homomorphic Encryption, Springer, 2021, pp. 31–62; IACR ePrint 2019/939, [https://eprint.iacr.org/2019/939](https://eprint.iacr.org/2019/939), Section 2.1.3.
