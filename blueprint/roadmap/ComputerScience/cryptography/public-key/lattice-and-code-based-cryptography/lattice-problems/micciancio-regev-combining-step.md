# Micciancio–Regev combining step: uniform SIS queries from Gaussian lattice samples

Let $L = L(B) \subset \mathbb{R}^n$ be a full-rank lattice with basis $B$, let $q \ge 2$, and let $s \ge \eta_\varepsilon(L)$, the smoothing parameter of $L$. Sample $y_1, \dots, y_m$ independently from a discrete Gaussian of width $s$ on the fine grid $q^{-1}L$, and let $c_i \in q^{-1}L / L \cong \mathbb{Z}_q^n$ be the coset of $y_i$ modulo $L$, written in the basis $B$; collect the $c_i$ as the columns of $C \in \mathbb{Z}_q^{n \times m}$. Then (i) the matrix $C$ is within statistical distance $m\varepsilon/2$ of uniform on $\mathbb{Z}_q^{n\times m}$, and conditionally on $c_i$ the vector $y_i$ is a discrete Gaussian over the coset $q^{-1}Bc_i + L$; (ii) for every $z \in \mathbb{Z}^m$ with $C z \equiv 0 \pmod q$, the combination $v = \sum_i z_i y_i$ lies in $L$, and $\|v\|_2 \le \|z\|_1 \cdot \max_i \|y_i\|_2 \le \sqrt m\,\|z\|_2 \cdot \max_i \|y_i\|_2$. Since $\max_i \|y_i\|_2 \le s\sqrt n$ with overwhelming probability, an $\ell_2$-SIS solution with $\|z\|_2 \le \beta$ for the (almost uniform) matrix $C$ yields a lattice vector of length at most $\beta s \sqrt{mn}$ deterministically from Cauchy–Schwarz; using the sharper probabilistic bound on the independent Gaussian combination $\sum_i z_i y_i$ in Micciancio and Regev (2007) removes the $\sqrt m$ factor, and iterating gives the worst-case to average-case reduction from $\mathrm{SIVP}_{\gamma}$ and $\mathrm{GapSVP}_\gamma$ with $\gamma = \tilde O(\beta \sqrt n)$ to $\mathrm{SIS}_{n,m,q,\beta}$.

## Proof sketch

Above the smoothing parameter a Gaussian modulo $L$ is $\varepsilon/2$-close to uniform on $\mathbb{R}^n/L$, so its rounding to $q^{-1}L/L$ is close to uniform on $\mathbb{Z}_q^n$. Linearity gives $\sum_i z_i y_i \in L$ whenever $Cz \equiv 0$, and the norm bound follows from Gaussian concentration and Cauchy–Schwarz.

## Depends on

- [The short integer solution problem in the Euclidean norm](sis-euclidean-norm.md)

## Sources

- Daniele Micciancio and Oded Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing, 2007.
