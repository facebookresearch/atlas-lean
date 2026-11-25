# delta-weakening is monotone

For a bounded existential formula $\varphi$ as on the δ-weakening page and rationals $0 < \delta \le \delta'$, every point satisfying
the matrix of $\varphi$ satisfies the matrix of $\varphi^\delta$, and every point satisfying the matrix of $\varphi^\delta$ satisfies that of
$\varphi^{\delta'}$. Hence $\varphi$ implies $\varphi^\delta$ and $\varphi^\delta$ implies $\varphi^{\delta'}$.

## Proof

The weakening replaces each atom by a weaker one: $t > 0$ implies $t > -\delta$, which implies $t > -\delta'$; likewise for $t \ge 0$; and
$t = 0$ implies $\lvert t \rvert \le \delta \le \delta'$. The matrix is a positive Boolean combination of atoms, so replacing atoms by weaker
ones weakens it (induction on the formula), and the bounded quantifiers range over the same boxes.

## Depends on

- [delta-weakening and delta-complete decision procedures](delta-weakening-and-delta-complete-decision-procedures.md)

## Sources

- S. Gao, J. Avigad and E. M. Clarke, *δ-complete decision procedures for satisfiability over the reals*, IJCAR 2012; arXiv:1204.3513, Section 1 ("if a formula is satisfiable, its δ-weakening is always satisfiable"). <https://arxiv.org/abs/1204.3513>
