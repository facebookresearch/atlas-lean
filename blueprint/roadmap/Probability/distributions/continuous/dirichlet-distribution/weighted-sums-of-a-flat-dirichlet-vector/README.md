# Distribution function of a weighted sum of a flat Dirichlet vector

Let $n \ge 1$, let $\theta = (\theta_0, \dots, \theta_n)$ have the flat Dirichlet law
$\operatorname{Dir}(1, \dots, 1)$ on $\mathbb{R}^{n+1}$, and let $w_0, \dots, w_n$ be pairwise distinct
real weights, of any signs and in any order. Then for every real $x$,

$$P\Bigl(\sum_{j=0}^n w_j \theta_j \le x\Bigr) = (-1)^n \sum_{j=0}^n \frac{\max(x - w_j, 0)^n}{\prod_{m \ne j} (w_j - w_m)} .$$

## Idea

The flat Dirichlet law is the uniform law on the simplex, so a weighted sum $\sum_j w_j \theta_j$ is a
random point of the interval spanned by the weights, and its distribution function is a piecewise
polynomial of degree $n$ with breakpoints at the weights: up to sign, the divided difference of the
truncated powers $\max(x - w, 0)^n$ at the nodes $w_0, \dots, w_n$. The proof integrates over the
simplex one coordinate at a time, with Tonelli's theorem and a change of scale, and partial-fraction
identities from Lagrange interpolation make the terms combine; the identity for $(x - X)^n$ explains
why the formula equals $1$ when $x$ lies above every weight.

## Statements

- [Distribution function of a weighted sum of a flat Dirichlet vector](dirichlet-measure-one-real-weighted-sum.md)
- [Partial fractions of the constant $1$](sum-inv-prod-erase-sub-eq-zero.md): algebraic lemma used in the proof
- [Partial fractions of $(x - X)^n$](sum-sub-pow-div-prod-erase-sub.md): the identity behind the value $1$ of the distribution function above every weight

## Background

- [Dirichlet distribution](../dirichlet-law/README.md): the flat Dirichlet law, and the Tonelli and scaling lemmas used in the proof
