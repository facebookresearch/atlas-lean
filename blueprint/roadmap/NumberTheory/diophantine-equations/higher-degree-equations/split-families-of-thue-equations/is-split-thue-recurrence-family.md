# Split Thue recurrence family

Let $d \in \mathbb{N}$, let $G_i(n)$ be integers for
$i, n \in \mathbb{N}$, and let $\gamma_i \in \mathbb{R}$ and $\delta_i \in \mathbb{C}$ for
$i \in \mathbb{N}$. Then $(d, G, \gamma, \delta)$ is a split Thue recurrence family when $d \ge 3$
and there are finite sets $R_i \subseteq \mathbb{C}$ and complex numbers $c_i(r)$
($i \in \mathbb{N}$, $r \in \mathbb{C}$) such that: for every $1 \le i \le d$, $c_i(r) \ne 0$
for all $r \in R_i$, $G_i(n) = \sum_{r \in R_i} c_i(r) r^n$ for all $n$, $\gamma_i \in R_i$,
and $|r| < \gamma_i$ for all $r \in R_i$ with $r \ne \gamma_i$; $\gamma_1 \ge 0$, $\gamma$ is
strictly increasing on $\{1, \dots, d - 1\}$, and $\gamma_{d-1} = \gamma_d$;
$c_{d-1}(\gamma_{d-1}) = c_d(\gamma_d)$; for $i \in \{d - 1, d\}$, $\delta_i \in R_i$,
$\delta_i \ne \gamma_i$, and $|r| < |\delta_i|$ for all $r \in R_i$ other than $\gamma_i$ and
$\delta_i$; and $|\delta_{d-1}| < |\delta_d| < \gamma_{d-2}$ and
$\gamma_{d-2}^2 < \gamma_d |\delta_d|$.

In words: each $G_i$ is a simple linear recurrence with dominant root $\gamma_i$, the sequences
$G_{d-1}$ and $G_d$ share their dominant root and its coefficient, and $\delta_{d-1}$, $\delta_d$
are their second dominant roots.

## Sources

- Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as Factors*, INTEGERS 25 (2025), Article A35, Theorem 1 (conditions 1-3); dominant roots taken real and nonnegative as in the paper's standing assumption after Corollary 1.
