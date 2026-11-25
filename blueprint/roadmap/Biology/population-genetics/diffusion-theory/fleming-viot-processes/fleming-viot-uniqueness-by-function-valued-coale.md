# Fleming–Viot uniqueness by moment duality

Let $E$ be a compact metric space and $B$ a bounded jump-type mutation operator on $C(E)$. The Fleming–Viot martingale problem on $\mathcal M_1(E)$ with polynomial test functions $\Phi_f(\mu) = \langle f, \mu^{\otimes n} \rangle$, $f \in C(E^n)$, $n \ge 0$, has at most one solution in law for each initial law. The argument has three steps:

1. for every solution, the moments $\mathbb E \langle f, X_t^{\otimes n} \rangle$ [satisfy the moment hierarchy](fleming-viot-martingale-problem-solutions-satisf.md), and the [hierarchy has a unique solution](fleming-viot-moment-hierarchy-triangular-bounded.md) for given initial moments, so the one-time moments of $X_t$ are determined by the initial law;
2. the polynomials $\Phi_f$ form a subalgebra of $C(\mathcal M_1(E))$ that contains the constants and separates points, so by the Stone–Weierstrass theorem they are dense, and since $\mathcal M_1(E)$ is compact their expectations determine the law of $X_t$;
3. the one-time marginals are therefore unique for every initial law, and [one-time marginal uniqueness implies uniqueness of finite-dimensional distributions](../../../../Probability/markov-chains/martingale-problems/from-one-time-marginal-uniqueness-to-fdd-uniquen.md) for the martingale problem.

For $n = 1$ the duality reads $\mathbb E \langle f, X_t \rangle = \langle e^{tB} f, \mu \rangle$ when $X_0 = \mu$; for finite $E$ it is the $K$-allele moment duality.

## Depends on

- [Fleming-Viot moment hierarchy: triangular bounded Volterra system and unique solvability](fleming-viot-moment-hierarchy-triangular-bounded.md)
- [Fleming-Viot martingale-problem solutions satisfy the moment hierarchy (bounded mutation)](fleming-viot-martingale-problem-solutions-satisf.md)
- [From one-time marginal uniqueness to fdd uniqueness for martingale problems](../../../../Probability/markov-chains/martingale-problems/from-one-time-marginal-uniqueness-to-fdd-uniquen.md)

## Proof depends on

- [Stone–Weierstrass theorem for star subalgebras](../../../../Topology/function-spaces/stone-weierstrass-star-subalgebra.md)
- [Prokhorov's theorem: tight sets of probability measures are relatively compact](../../../../Probability/convergence-of-measures/prokhorov-theorem-on-a-polish-space.md)

## Expansion

A full proof page must still establish:

- that the polynomials separate the points of $\mathcal M_1(E)$ and the density argument on the compact space $\mathcal M_1(E)$ with the weak topology;
- the cases $n = 1$ and finite $E$.

## Sources

- D. A. Dawson, "Measure-valued Markov processes", in *École d'Été de Probabilités de Saint-Flour XXI–1991*, Lecture Notes in Mathematics 1541, Springer, 1993, duality for Fleming–Viot, <https://link.springer.com/chapter/10.1007/BFb0084190>
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 4 (duality), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>
