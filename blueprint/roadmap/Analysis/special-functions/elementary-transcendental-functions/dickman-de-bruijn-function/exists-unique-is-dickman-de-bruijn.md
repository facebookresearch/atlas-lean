# Existence and uniqueness of the Dickman–de Bruijn function

There is exactly one function
$\rho : \mathbb{R} \to \mathbb{R}$ that is a Dickman–de Bruijn function, that is, such that
$\rho(u) = 0$ for $u < 0$, $0 \le \rho(u) \le 1$ for $u \ge 0$, $\rho$ is continuous on
$[0, \infty)$, $\rho(u) = 1$ for $0 \le u \le 1$, and for every $u > 1$ the function $\rho$ is
differentiable at $u$ with $u \rho'(u) + \rho(u - 1) = 0$.

## Sources

- [O. Gorodetsky, *Rigidity of Averages over the Two Largest Prime Factors*](https://arxiv.org/abs/2608.05191), which characterizes the unique continuous function on the nonnegative reals and specifies its zero extension to negative inputs; Lean packages those clauses in `Real.IsDickmanDeBruijn`.
