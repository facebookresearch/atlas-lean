# The Brjuno function is not computable at some Brjuno number

There is an irrational number $x \in (0,1)$ with finite Brjuno function value $\mathcal{B}(x)$ such that no oracle Turing machine computes $\mathcal{B}(x)$ to arbitrary precision from approximations of $x$.

For an irrational $\theta \in (0,1)$ let $\theta_{-1} = 1$, $\theta_0 = \theta$ and $\theta_{i+1} = \{1/\theta_i\}$ (the Gauss map). The *Brjuno function* of Yoccoz is

$$
\mathcal{B}(\theta) = \sum_{n \ge 0} \theta_{-1} \theta_0 \theta_1 \cdots \theta_{n-1} \log \frac{1}{\theta_n} \in (0, +\infty] ,
$$

and the irrationals with $\mathcal{B}(\theta) < +\infty$ are the *Brjuno numbers*, a set of full measure. An *oracle* for $x \in \mathbb{R}$ is a function $\phi$ from $\mathbb{N}$ to the dyadic rationals with $|\phi(n) - x| < 2^{-n}$ for all $n$. A function $f$ is *computable at* $x$ if there is an oracle Turing machine $M^\phi$ that, on input $n$ and with any oracle $\phi$ for $x$, outputs a dyadic $d_n$ with $|f(x) - d_n| < 2^{-n}$.

**Theorem.** There exists an irrational $x \in (0,1)$ with $\mathcal{B}(x) < +\infty$ such that $\mathcal{B}$ is not computable at $x$ (Theorem 5.2 of the source, which applies to $\mathcal{B}$ by Theorem 5.1; the theorem gives a point of the domain at which $\mathcal{B}$ is not computable, and its proof shows that $\mathcal{B}$ is finite there).

The source proves this for a class of generalized Brjuno functions defined by ergodic sampling of expanding interval maps with weights, which by Theorem 5.1 contains $\mathcal{B}$, the first and second Wilton functions and the $\alpha$-continued-fraction Brjuno functions $\mathcal{B}_{\alpha,u,\nu}$ under stated conditions on $u$.

## Depends on

None.

## Proof depends on

None.

## Expansion

The proof diagonalizes against all oracle Turing machines. It starts from the golden mean $[1, 1, 1, \ldots]$ and, at stage $i$, takes the next machine in an enumeration that appears to compute the function near the current point. Replacing a far-out continued fraction digit by a large integer $N$ moves the point by an arbitrarily small amount but makes the corresponding term of the series, and hence the function value, as large as desired as $N \to \infty$; choosing the digit so that the machine's committed output is wrong, while keeping all later modifications small, defines a limit point $x_\infty$ with $\mathcal{B}(x_\infty) < +\infty$ at which every machine fails. Separately, the source shows that $\mathcal{B}$ maps computable numbers onto left-computable values: for every left-computable $y \ge \mathcal{B}((\sqrt{5}-1)/2)$ there is a computable $x \in (0,1)$ with $\mathcal{B}(x) = y$ (Corollary 3.4), a result distilled from work of Braverman and Yampolsky on Julia sets, so $\mathcal{B}$ takes non-computable values at computable points.

## Sources

- M. Yampolsky and I. O. Shevchenko, "Computability of Brjuno-like functions", Canadian Journal of Mathematics (2025), 1–41, https://doi.org/10.4153/S0008414X2510179X; read in arXiv:2501.04195v1 (the definitions of oracles and computability in Section 2, Corollary 3.4, and Theorems 5.1 and 5.2 of arXiv:2501.04195v1).
