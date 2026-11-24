# The Servedio–Tan–Verbin conjecture is false

Order $\{0,1\}^n$ coordinatewise with
$0 < 1$, and write $\deg f$ for the Boolean degree of a function $f : \{0,1\}^n \to \{0,1\}$. It
is not the case that for every real $\varepsilon > 0$ there is a natural number $C$ such that for
every $n \in \mathbb{N}$ and every monotone $f : \{0,1\}^n \to \{0,1\}$ there are a set $J$ of at
most $(\deg f + 2)^C$ coordinates and a function $g : \{0,1\}^n \to \{0,1\}$ that depends only on
the coordinates in $J$ such that $f(x) \ne g(x)$ for at most $\varepsilon 2^n$ points
$x \in \{0,1\}^n$.

Kane constructed, for a fixed $\varepsilon > 0$, a constant $c > 0$ and every $d$, monotone
functions of decision-tree depth $d$ (hence degree at most $d$) that are $\varepsilon$-far from
every junta on $\exp(c \sqrt{d})$ coordinates; since $\exp(c \sqrt{d})$ eventually exceeds
$(d + 2)^C$, no polynomial junta size works for $\varepsilon / 2$. O'Donnell's list records the
conjecture as resolved in the negative by Kane.

## Sources

- R. O'Donnell, Open Problems in Analysis of Boolean Functions (2012), arXiv:1204.6447, Problem 24 (Servedio–Tan–Verbin Conjecture); resolution: D. M. Kane, A low-depth monotone function that is not an approximate junta, arXiv:1206.6541 (2012); recorded as "RESOLVED (in the negative) by Daniel Kane, 2012" in O'Donnell's list, Problem 24, Kane, Theorem 2: there is a constant ε > 0 such that for every d there are k = exp(Ω(√d)) and a monotone f : {0,1}ⁿ → {0,1} computed by a depth-d decision tree (so deg f ≤ d) that disagrees with every k-junta on at least an ε-fraction of inputs, https://arxiv.org/abs/1206.6541.
