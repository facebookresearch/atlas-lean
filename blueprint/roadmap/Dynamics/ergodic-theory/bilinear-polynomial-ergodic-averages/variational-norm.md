# Variational norm

For a real number $r \ge 0$ and a sequence
$a = (a_n)_{n \in \mathbb{N}}$ of complex numbers, the $r$-variational norm of $a$ is the
element of $[0, \infty]$

$$\|a\|_{\mathbb{V}^r} = \sup_{n \in \mathbb{N}} |a_n| +
\sup_{J \in \mathbb{N}} \sup_{N_0 \le N_1 \le \dots \le N_J}
\Big( \sum_{j=0}^{J-1} |a_{N_{j+1}} - a_{N_j}|^r \Big)^{1/r},$$

where the inner supremum runs over nondecreasing finite sequences of natural numbers
$N_0 \le N_1 \le \dots \le N_J$ and the empty sum ($J = 0$) is $0$. For $r = 0$ the whole term
$\big( \sum_{j=0}^{J-1} |a_{N_{j+1}} - a_{N_j}|^r \big)^{1/r}$ is replaced by the number of
indices $j < J$ with $a_{N_{j+1}} \ne a_{N_j}$.
