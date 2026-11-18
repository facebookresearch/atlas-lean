# Exact matrix completion (Candès–Recht)

There are numerical constants $C, c > 0$ such that the following holds. Let
$M = U \operatorname{diag}(\sigma) V^{\mathsf T}$ be an $n_1 \times n_2$ matrix of rank $r \ge 1$,
where $U \in \mathbb{R}^{n_1 \times r}$ and $V \in \mathbb{R}^{n_2 \times r}$ have orthonormal columns
and $\sigma_k > 0$ for every $k$, and put $n = \max(n_1, n_2)$. Assume

* **A0**: the coherences of the column and row spaces obey $\max(\mu(U), \mu(V)) \le \mu_0$, where
  $\mu(U) = \frac{n_1}{r} \max_i \|P_U e_i\|^2 = \frac{n_1}{r} \max_i \sum_k U_{ik}^2$
  (Definition 1.2);
* **A1**: every entry of $U V^{\mathsf T} = \sum_k u_k v_k^{\mathsf T}$ is at most
  $\mu_1 \sqrt{r / (n_1 n_2)}$ in absolute value, with $\mu_1 \ge 1$.

If $\beta > 2$ and
$m \ge C \max\big(\mu_1^2, \mu_0^{1/2} \mu_1, \mu_0 n^{1/4}\big)\, n r\, (\beta \log n)$, then for a
set $\Omega$ of $m$ entries drawn uniformly at random among the $\binom{n_1 n_2}{m}$ such sets, $M$
is the unique minimizer of the nuclear norm over
$\{X : X_{ij} = M_{ij} \text{ for } (i, j) \in \Omega\}$ with probability at least
$1 - c\, n^{-\beta}$.

The sampling operator of matrix completion has no restricted isometry property on low-rank
matrices, so the proof in the source does not go through restricted isometry: it constructs a dual
certificate for the nuclear norm at $M$, using that the projected sampling operator is close to an
isometry on the tangent space of the rank-$r$ matrices at $M$ (a Rudelson-type concentration
bound), which is where incoherence enters.

## Background

- [Exact recovery by nuclear norm minimization under restricted isometry](nuclear-norm-lt-of-is-restricted-isometr.md): the same convex program, analysed under a restricted isometry property that random Gaussian measurements satisfy but entry sampling does not.
- [Nuclear norm](nuclear-norm.md): the objective minimized.

## Sources

- E. J. Candès and B. Recht, *Exact matrix completion via convex optimization*, Found. Comput. Math. 9 (2009) 717-772, arXiv:0805.4471, Theorem 1.3 (first part), with Definition 1.2 and assumptions A0, A1 of Section 1.2; the standing assumption $\mu_1 \ge 1$ is stated there just before the theorem. The improvement $m \ge C \mu_0 n^{6/5} r (\beta \log n)$ for $r \le \mu_0^{-1} n^{1/5}$ (second part) is not included here.
