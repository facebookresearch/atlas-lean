# Reduction from the uniform integral bound

Fix a finite ground set $X$. Suppose that for every $r\ge 1$ and every nonempty family $H$ of
subsets of $X$ of size at most $r$, with $\varnothing\notin H$, the following bound holds:

$$
\sup\{p\in(0,1):\mu_p(\langle H\rangle)\le 1/2\}
\le 6q_c(\langle H\rangle)\log_2(2r).
$$

Here $\mu_p$ is the $p$-biased product measure, $\langle H\rangle$ is the upward closure of $H$,
and the supremum is in $[0,1]$. Then every increasing family $\mathcal F$ on $X$ whose largest
minimal member has size $\ell\ge 2$ satisfies

$$
p_c(\mathcal F)\le \frac{12}{\ln 2}\,q_f(\mathcal F)\ln\ell.
$$

Take $H$ to consist of the minimal members of $\mathcal F$. Finiteness gives
$\langle H\rangle=\mathcal F$; the rank condition ensures that $H$ is nonempty and does not
contain the empty set. Now use $q_c\le q_f$ and $\ln(2\ell)\le 2\ln\ell$.

## Sources

- Bryan Park and Jan Vondrák, [*A simple proof of the non-uniform Kahn–Kalai conjecture*](https://arxiv.org/abs/2306.12576), §2.3, the uniform bound with $L=6$ on p. 6.
