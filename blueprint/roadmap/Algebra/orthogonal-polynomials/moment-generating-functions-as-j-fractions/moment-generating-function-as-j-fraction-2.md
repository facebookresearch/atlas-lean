# Moment generating function as a J-fraction

Let $p_0, p_1, \dots$ be real polynomials, each
$p_n$ monic of degree $n$, let $L$ be an $\mathbb{R}$-linear functional on $\mathbb{R}[x]$, and
let $(\alpha_n)$, $(\beta_n)$ and $(\mu_k)$ be real sequences. Suppose that $p_0 = 1$,
$p_1 = x - \alpha_0$ and $p_{n+1} = (x - \alpha_n) p_n - \beta_n p_{n-1}$ for $n \ge 1$, that
$\beta_n \ne 0$ for $n \ge 1$, that the $p_n$ are orthogonal for $L$, meaning $L(p_m p_n) = 0$
for $m \ne n$ and $L(p_n^2) \ne 0$ for every $n$, that $\mu_k = L(x^k)$ for every $k$, and that
$\mu_0 \ne 0$. Let $g = \sum_{k \ge 0} \mu_k x^k$ be the moment generating function. Then there
are formal power series $S_0, S_1, \dots$ over $\mathbb{R}$, each with constant term $1$, such
that $g = \mu_0 S_0$ and $S_n (1 - \alpha_n x - \beta_{n+1} x^2 S_{n+1}) = 1$ for every
$n \ge 0$.

These equations present $g$ as the J-fraction
$\mu_0 / (1 - \alpha_0 x - \beta_1 x^2 / (1 - \alpha_1 x - \beta_2 x^2 / \cdots))$ with tails
$S_n$. The hypotheses that each $p_n$ is monic of degree $n$, that $\beta_n \ne 0$, that
$L(p_n^2) \ne 0$ and that $\mu_0 \ne 0$ are not needed, and orthogonality is used only through
$L(p_n) = 0$ for $n \ge 1$.

The source's recurrence line reads $\beta_n(x)$; it is read as $\beta_n p_{n-1}$, as in the
surrounding lines 315–317 and 364–366 of the source.

## Sources

- Paul Barry and Aoife Hennessy, "Meixner-Type Results for Riordan Arrays and Associated Integer Sequences," Journal of Integer Sequences 13 (2010), Article 10.9.4, J-fraction theorem citing C. Krattenthaler (cf. Viennot Proposition 1, (7), p. V-5; Wall Theorem 51.1), lines 353–362, https://cs.uwaterloo.ca/journals/JIS/VOL13/Barry5/barry96s.tex
