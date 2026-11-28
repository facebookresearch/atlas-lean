# The Lasserre / sum-of-squares hierarchy for Boolean polynomial optimization

Let $p, q_1, \dots, q_m \in \mathbb{R}[x_1, \dots, x_n]$ and consider maximizing $p(x)$ over the feasible set $F = \{x \in \{0,1\}^n : q_j(x) = 0 \text{ for all } j\}$, assumed nonempty. Since $x_i^2 = x_i$ on $\{0,1\}^n$, first replace $p$ and every $q_j$ by its multilinear reduction (each power $x_i^a$ with $a \ge 1$ becomes $x_i$), which changes no value on $\{0,1\}^n$; without this step a constraint such as $x_1^3 = 0$ with $n = 1$ and $d = 2$ would exceed the degree bound and be dropped, although on $\{0,1\}$ it means $x_1 = 0$. For an integer $d \ge \max(2, \deg p, \deg q_1, \dots, \deg q_m)$, degrees taken after reduction, the **degree-$d$ sum-of-squares (Lasserre) relaxation** is the semidefinite program

$$
\mathrm{SoS}_d = \max\Bigl\{\, \tilde{\mathbb{E}}[p] \;:\; \tilde{\mathbb{E}} : \mathbb{R}[x]_{\le d} \to \mathbb{R} \text{ linear},\ \tilde{\mathbb{E}}[1] = 1,\ \tilde{\mathbb{E}}[(x_i^2 - x_i) r] = 0,\ \tilde{\mathbb{E}}[q_j r] = 0,\ \tilde{\mathbb{E}}[s^2] \ge 0 \,\Bigr\},
$$

with constraints truncated at degree $d$: they range over all $i$ and $j$, all polynomials $r$ with $\deg r \le d - 2$ in the Boolean constraints and $\deg r \le d - \deg q_j$ in the $j$-th equality constraint, and all polynomials $s$ with $2 \deg s \le d$. Its value is at least the true maximum, is non-increasing in $d$, and equals the maximum for every $d \ge 2n + \max_j \deg q_j$; with no constraints $q_j$, total degree $d \ge 2n$ suffices, since every function nonnegative on $\{0,1\}^n$ is a degree-$2n$ sum of squares there. Fleming, Kothari and Pitassi index the hierarchy by level, level $d$ meaning total degree $2d$, so their exactness at level $n + \deg(P)/2$ is total degree $2n + \deg(P)$. The relaxation is practically solvable in time $n^{O(d)}$ under polynomial bit-length assumptions on the coefficients. By duality, $\mathrm{SoS}_d \le c$ certifies $p \le c$ on the feasible Boolean points via a degree-$d$ sum-of-squares identity.

## Sources

- J. B. Lasserre, "Global optimization with polynomials and the problem of moments", SIAM Journal on Optimization 11 (2001) 796-817.
- P. A. Parrilo, "Structured semidefinite programs and semialgebraic geometry methods in robustness and optimization", PhD thesis, Caltech (2000).
- N. Fleming, P. Kothari, T. Pitassi, "Semialgebraic proofs and efficient algorithm design", Foundations and Trends in Theoretical Computer Science 14 (2019), ECCC TR19-106 revision 3, Section 1 (practical degree automatability under bit-length assumptions), Lemma 3.35 (degree $2n$ suffices for nonnegativity on $\{0,1\}^n$), Lemma 3.43 (relaxation, monotonicity, exactness at level $n + \deg(P)/2$) and Definition 3.44 (level-$d$, degree-$2d$ pseudo-expectations).
