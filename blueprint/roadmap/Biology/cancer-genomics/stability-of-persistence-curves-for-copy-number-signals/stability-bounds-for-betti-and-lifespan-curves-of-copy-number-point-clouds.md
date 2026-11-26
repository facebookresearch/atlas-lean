# Stability bounds for Betti and lifespan curves of copy-number point clouds

**Persistence curves.** For a persistence diagram $D$ in homological dimension $i$, the Betti curve $\beta_i(D,t)$ counts the pairs $(b,d)\in D$ with $t\in(b,d]$, and the lifespan curve $\ell_i(D,t)$ sums $d-b$ over the same pairs. In dimension $0$, reduced homology is used, which removes the infinite class. Let $n_C$ be the number of pairs of $C$, $L_C$ the sum of their lifespans, and $W_\infty$ the bottleneck distance.

**General bound.** For persistence diagrams $C,D$,

$$\|\beta(C,\cdot)-\beta(D,\cdot)\|_1\le2\max(n_C,n_D)\,W_\infty(C,D)+\min(L_C,L_D),\qquad \|\ell(C,\cdot)-\ell(D,\cdot)\|_1\le2(L_C+L_D)\,W_\infty(C,D).$$

For a finite point cloud of diameter $d$, every Vietoris–Rips or Čech persistence pair has lifespan at most $d$, and the number of pairs is finite. So both curves are bounded under small perturbations of the points.

**Theorem (sliding-window copy-number data).** Copy-number ratios lie in $[c_{\min},c_{\max}]$. A sliding-window embedding with window size $s$ therefore lies in $[c_{\min},c_{\max}]^s$, and its diameter is at most $d=\sqrt s\,(c_{\max}-c_{\min})$. Let $P,P'$ be two such clouds of $n$ points each, with diagrams $C,D$, and let $N_1(n)=\lfloor n/2\rfloor\lceil n/2\rceil-(n-1)$. For $1$-dimensional Vietoris–Rips persistence with pairwise-distinct distances,

$$\|\beta_1(C,\cdot)-\beta_1(D,\cdot)\|_1\le N_1(n)\bigl(2W_\infty(C,D)+\sqrt s\,(c_{\max}-c_{\min})\bigr),$$

$$\|\ell_1(C,\cdot)-\ell_1(D,\cdot)\|_1\le4N_1(n)\,\sqrt s\,(c_{\max}-c_{\min})\,W_\infty(C,D).$$

For $0$-dimensional Vietoris–Rips or Čech persistence, where at most $n$ components occur,

$$\|\beta_0(C,\cdot)-\beta_0(D,\cdot)\|_1\le n\bigl(2W_\infty(C,D)+\sqrt s\,(c_{\max}-c_{\min})\bigr),\qquad \|\ell_0(C,\cdot)-\ell_0(D,\cdot)\|_1\le4n\sqrt s\,(c_{\max}-c_{\min})\,W_\infty(C,D).$$

## Depends on

- [Maximal number of one-dimensional Vietoris–Rips persistence pairs](maximal-number-of-one-dimensional-vietoris-rips-persistence-pairs.md)

## Expansion

Insert into the general bound the cap on the number of pairs ($N_1(n)$ in dimension $1$, $n$ in dimension $0$) and the cap $L\le(\text{number of pairs})\cdot d$ on total lifespan. Beyond scale $d$, every ball contains the whole cloud, so the complex is a contractible simplex and every class has died. Because $W_\infty$ is itself stable under perturbations of the points, the bounds make lifespan curves conditionally stable and quantify the instability of Betti curves. These bounds compare one test patient with one control patient. In the TAaCGH association test, per-patient curves are averaged within the test and control groups, and the $L^2$ norm of the difference of the averages is used as a permutation-test statistic. Because persistence diagrams have no mean, the bounds do not transfer to the averaged curves.

## Sources

- J. Aslam, S. Ardanza-Trevijano, J. Xiong, J. Arsuaga, R. Sazdanovic, "TAaCGH suite for detecting cancer-specific copy number changes using topological signatures", *Entropy* 24(7):896 (2022), Section 2.1 (persistence curves), Section 2.2 (TAaCGH test), Section 3, Theorem 1 (Eqs. 1–2), Propositions 1–2, Theorems 2–4, <https://doi.org/10.3390/e24070896>, PMCID PMC9318413.
