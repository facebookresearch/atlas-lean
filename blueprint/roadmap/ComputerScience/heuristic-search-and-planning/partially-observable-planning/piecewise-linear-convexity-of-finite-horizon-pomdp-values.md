# Piecewise-linear convexity of finite-horizon POMDP values

For a finite POMDP with reward maximization and terminal reward $0$, and every horizon $H \ge 0$, there is a
finite set $\Gamma_H$ of vectors in $\mathbb{R}^S$ such that the optimal $H$-step value satisfies
$V_H(b) = \max_{\alpha \in \Gamma_H} \sum_s b(s) \alpha(s)$ for every belief $b$; hence $V_H$ is piecewise
linear and convex on the belief simplex. One can take $\Gamma_0 = \{0\}$ and obtain $\Gamma_{H+1}$ from
$\Gamma_H$ by choosing an action and, for each observation, a vector of $\Gamma_H$. The statement is for
finite horizons; infinite-horizon discounted values are a separate matter.

## Depends on

- [Finite POMDPs](finite-pomdps.md)
- [Belief update](belief-update.md)

## Proof depends on

- [Belief MDP equivalence (finite horizon)](belief-mdp-equivalence.md)

## Sources

- L. P. Kaelbling, M. L. Littman and A. R. Cassandra, *Planning and acting in partially observable stochastic domains*, Artificial Intelligence 101 (1998) 99–134, Section 4: $t$-step policy trees, their value vectors $\alpha$, and the finite-horizon optimal value as the upper surface of finitely many linear functions of the belief, hence piecewise-linear and convex (Sections 4.1–4.2); Section 4 also notes that this need not hold for infinite-horizon discounted values. <https://cs.brown.edu/courses/csci2951-k/papers/kaelbling98.pdf>
