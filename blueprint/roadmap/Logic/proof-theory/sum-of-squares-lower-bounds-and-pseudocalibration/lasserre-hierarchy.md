# The Lasserre / sum-of-squares hierarchy for Boolean polynomial optimization

Let $p, q_1, \dots, q_m \in \mathbb{R}[x_1, \dots, x_n]$ and consider maximizing $p(x)$ over the feasible set $F = \{x \in \{0,1\}^n : q_j(x) = 0 \text{ for all } j\}$, assumed nonempty. Since $x_i^2 = x_i$ on $\{0,1\}^n$, first replace $p$ and every $q_j$ by its multilinear reduction (each power $x_i^a$ with $a \ge 1$ becomes $x_i$), which changes no value on $\{0,1\}^n$; without this step a constraint such as $x_1^3 = 0$ with $n = 1$ and $d = 2$ would exceed the degree bound and be dropped, although on $\{0,1\}$ it means $x_1 = 0$. For an integer $d \ge \max(2, \deg p, \deg q_1, \dots, \deg q_m)$, degrees taken after reduction, the **degree-$d$ sum-of-squares (Lasserre) relaxation** is the semidefinite program

$$
\mathrm{SoS}_d = \max\Bigl\{\, \tilde{\mathbb{E}}[p] \;:\; \tilde{\mathbb{E}} : \mathbb{R}[x]_{\le d} \to \mathbb{R} \text{ linear},\ \tilde{\mathbb{E}}[1] = 1,\ \tilde{\mathbb{E}}[(x_i^2 - x_i) r] = 0,\ \tilde{\mathbb{E}}[q_j r] = 0,\ \tilde{\mathbb{E}}[s^2] \ge 0 \,\Bigr\},
$$

with constraints truncated at degree $d$: they range over all $i$ and $j$, all polynomials $r$ with $\deg r \le d - 2$ in the Boolean constraints and $\deg r \le d - \deg q_j$ in the $j$-th equality constraint, and all polynomials $s$ with $2 \deg s \le d$. Its value is at least the true maximum, is non-increasing in $d$, equals the maximum for every $d \ge 2n$, and can be computed to additive precision $\eta$ in time $n^{O(d)} \operatorname{polylog}(1/\eta)$ under bit-complexity conditions. By duality, $\mathrm{SoS}_d \le c$ certifies $p \le c$ on the feasible Boolean points via a degree-$d$ sum-of-squares identity.

## Sources

- J. B. Lasserre, "Global optimization with polynomials and the problem of moments", SIAM Journal on Optimization 11 (2001) 796-817.
- P. A. Parrilo, "Structured semidefinite programs and semialgebraic geometry methods in robustness and optimization", PhD thesis, Caltech (2000).
- N. Fleming, P. Kothari, T. Pitassi, "Semialgebraic proofs and efficient algorithm design", Foundations and Trends in Theoretical Computer Science 14 (2019).
