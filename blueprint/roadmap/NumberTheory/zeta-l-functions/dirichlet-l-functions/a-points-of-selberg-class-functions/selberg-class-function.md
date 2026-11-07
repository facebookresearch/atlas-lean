# Functions in the Selberg class

A function in the Selberg class consists of Dirichlet
coefficients $a \colon \mathbb{N} \to \mathbb{C}$, a function $F \colon \mathbb{C} \to \mathbb{C}$,
a number $r \in \mathbb{N}$ of Gamma factors, a conductor $Q > 0$, real numbers
$\lambda_1, \dots, \lambda_r > 0$, complex numbers $\mu_1, \dots, \mu_r$ with
$\operatorname{Re} \mu_j \ge 0$ and a root number $\omega \in \mathbb{C}$ with $|\omega| = 1$,
such that:

- $a(1) = 1$;
- for every $s$ with $\operatorname{Re} s > 1$ the Dirichlet series $\sum_{n \ge 1} a(n) n^{-s}$
  converges absolutely and equals $F(s)$;
- (Ramanujan hypothesis) for every $\varepsilon > 0$ there is a constant $C$ with
  $|a(n)| \le C n^{\varepsilon}$ for all $n$;
- (Euler product) there are $b \colon \mathbb{N} \to \mathbb{C}$ with $b(n) = 0$ unless $n$ is a
  prime power, a real $\theta < 1/2$ and a constant $C$ with $|b(n)| \le C n^{\theta}$ for all $n$,
  and a real $\sigma_0$ such that for every $s$ with $\operatorname{Re} s > \sigma_0$ the series
  $\sum_{n \ge 1} b(n) n^{-s}$ converges absolutely and $F(s) = \exp \sum_{n \ge 1} b(n) n^{-s}$;
- (analytic continuation) there are $m \in \mathbb{N}$, an entire function $g$ and real numbers
  $\rho$, $A$ with $|g(s)| \le A e^{|s|^{\rho}}$ for all $s$ (so $g$ has finite order) and
  $g(s) = (s - 1)^m F(s)$ for all $s \ne 1$;
- (functional equation) with $\Phi(s) = F(s) Q^s \prod_{j=1}^r \Gamma(\lambda_j s + \mu_j)$, the
  identity $\Phi(s) = \omega \overline{\Phi(1 - \bar s)}$ holds for every $s \ne 0, 1$ such that
  for no $j$ is $\lambda_j s + \mu_j$ or $\lambda_j (1 - \bar s) + \mu_j$ an integer $\le 0$.

## Sources

- M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11, Section 2.
