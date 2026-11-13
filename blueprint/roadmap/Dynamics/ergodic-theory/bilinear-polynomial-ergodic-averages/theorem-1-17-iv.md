# Long variational inequality for bilinear polynomial averages

Let $(X, \mu)$ be a
$\sigma$-finite measure space and let $T : X \to X$ be a measurable bijection with measurable
inverse that preserves $\mu$. Let $P \in \mathbb{Z}[t]$ have degree at least $2$, and let
$p_1, p_2 \in (1, \infty)$ and $p \in [0, \infty]$ satisfy $p_1^{-1} + p_2^{-1} = p^{-1}$ and
$p^{-1} \le 1$. For a real number $N \ge 0$, functions $f, g : X \to \mathbb{C}$ and $x \in X$ let

$$A_N(f, g)(x) = \frac{1}{\lfloor N \rfloor}
\sum_{n=1}^{\lfloor N \rfloor} f(T^n x)\, g(T^{P(n)} x),$$

with $A_N(f, g)(x) = 0$ when $\lfloor N \rfloor = 0$, where $T^k$ for $k \in \mathbb{Z}$ is the
$k$-th power of $T$ in the group of bijections of $X$. Then
for all real numbers $r > 2$ and $\Lambda > 1$ there is a constant $C \ge 0$, which may depend
on $r$, $\Lambda$ and all of the data above, such that for all $f \in L^{p_1}(\mu)$ and
$g \in L^{p_2}(\mu)$ with values in $\mathbb{C}$ and every $\Lambda$-lacunary sequence
$(a_n)_{n \in \mathbb{N}}$ of nonnegative reals (that is, $a_{n+1} / a_n > \Lambda$ for all $n$)
with $a_n \ge 1$ for all $n$,

$$\Big\| x \mapsto \big\| (A_{a_n}(f, g)(x))_{n \in \mathbb{N}} \big\|_{\mathbb{V}^r}
\Big\|_{L^p(\mu)} \le C \, \|f\|_{L^{p_1}(\mu)} \, \|g\|_{L^{p_2}(\mu)},$$

where $\| \cdot \|_{\mathbb{V}^r}$ is the $r$-variational norm of a sequence of complex numbers.

This is Theorem 1.17(iv) of Krause, Mirek and Tao.

## Sources

- B. Krause, M. Mirek, and T. Tao, `Pointwise ergodic theorems for non-conventional bilinear polynomial averages`, Annals of Math, 195 (3) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_pointwise_ergodic_theorems` of the lean-eval benchmark.
