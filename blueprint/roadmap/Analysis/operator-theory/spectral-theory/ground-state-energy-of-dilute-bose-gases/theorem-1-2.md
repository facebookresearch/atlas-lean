# Lee–Huang–Yang lower bound for dilute Bose gases

There are a real number $\eta$ and a
function $\mathcal{C}$ of two real variables such that the following holds. Let
$v : \mathbb{R}^3 \to \mathbb{R}$ be a non-negative, radial, integrable potential that is not
almost everywhere zero, and let $R > 0$ be such that the closed support of $v$ lies in the open
ball $B(0, R)$. Let $a$ be the scattering length of $v$, let $\mathcal{R}(v) = \int v/(8\pi a)$,
and let $e(\rho, v)$ be the ground state energy density at density $\rho$: the limit, as
$L \to \infty$ and $N/L^3 \to \rho$, of $L^{-3}$ times the infimum, over
$\Psi \in C_0^\infty(([0,L]^3)^N) \setminus \{0\}$, of
$\langle \Psi, H_N \Psi \rangle / \|\Psi\|^2$, where the inner product and norm are those of
$L^2(([0,L]^3)^N)$ and, writing points of $(\mathbb{R}^3)^N$ as $(x_1, \dots, x_N)$ and
$\Delta_{x_i}$ for the Laplacian in the variable $x_i$,
$H_N = \sum_{i=1}^{N} -\Delta_{x_i} + \sum_{1 \le i < j \le N} v(x_i - x_j)$. Then
$\eta > 0$, and for all sufficiently small $\rho > 0$,

$$
e(\rho, v) \ge 4\pi\rho^2 a \left(1 + \frac{128}{15\sqrt{\pi}}\sqrt{\rho a^3} -
\mathcal{C}(\mathcal{R}(v), R/a)\,(\rho a^3)^{1/2 + \eta}\right).
$$

The source takes the limit $\rho a^3 \to 0^+$; for fixed $v$ this is the same as $\rho \to 0^+$.
Although the wording of Theorem 1.2 in the source suggests that $\eta$ may depend on
$\mathcal{R}(v)$ and $R/a$, Theorem 6.8 there shows that $\eta$ is a universal constant.

## Sources

- S. Fournais and J. P. Solovej, `The energy of dilute Bose gases`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-BoseGases.lean Via leanprover/lean-eval@38361be, problem `annals_bose_gases`.
