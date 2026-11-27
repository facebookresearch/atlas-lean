# Whether the ground-state energy density is zero is undecidable

No algorithm decides, for a translation-invariant nearest-neighbor Hamiltonian on the square lattice from an explicit one-parameter family with fixed local dimension and algebraic entries, whether its ground-state energy density is zero or positive.

**Theorem (Cubitt, Perez-Garcia and Wolf).** Let $d\in\mathbb N$ be sufficiently large but fixed. One can construct explicitly a one-parameter family, indexed by $n\in\mathbb N$, of [translation-invariant nearest-neighbor Hamiltonians](translation-invariant-lattice-hamiltonians.md) on the square lattice with open boundary conditions, local dimension $d$, algebraic matrix entries and local interaction strength at most $1$, each of whose ground-state energy density

$$
E_\rho=\lim_{L\to\infty}\frac{\lambda_0(H^{\Lambda(L)})}{L^2}
$$

satisfies either $E_\rho=0$ or $E_\rho>0$, such that determining which of the two holds is undecidable.

In the construction, $E_\rho=0$ exactly when a fixed universal Turing machine does not halt on input $n$, and $E_\rho>0$ when it halts; in the halting case the source bounds the ground-state energy below through positive functions $\delta_1(n),\delta_2(n)$ that it notes are uncomputable. The same holds with periodic boundary conditions.

## Depends on

- [Translation-invariant nearest-neighbor lattice Hamiltonians](translation-invariant-lattice-hamiltonians.md)
- [Hypercubic lattice $\mathbb{Z}^d$](../../../../GraphTheory/graph-families-and-operations/hypercubic-lattice-graphs/hypercubic-lattice.md)
- [Halting of a code on an input](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/halts.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

A quantum Turing machine of fixed size reads the input $n$ from a phase in the interactions by quantum phase estimation and then runs the universal machine; the translation-invariant history-state construction of Gottesman and Irani turns it into a one-dimensional Hamiltonian whose ground-state energy on a segment of length $L$ is $0$ when the machine does not halt within the available space and time, and positive when it does. Placing these segments on the squares of every size of Robinson's aperiodic tiling, enforced by a classical tiling Hamiltonian, and shifting the energy by a small multiple of the identity gives interactions for which either $\lambda_0(H^{\Lambda(L)})\le-L\beta/2$ for all $L$ (non-halting) or $\lambda_0(H^{\Lambda(L)})\ge L^2\delta_2(n)-L\delta_1(n)$ for all large $L$ with $\delta_1(n),\delta_2(n)>0$ (halting); dividing by $L^2$ gives the two cases for $E_\rho$. A good expansion links pages for Robinson's tiling, the history-state construction with the Gottesman–Irani clock, well-formed quantum Turing machines and quantum phase estimation; none of these has a page yet.

## Sources

- T. Cubitt, D. Perez-Garcia and M. M. Wolf, "Undecidability of the spectral gap", *Forum of Mathematics, Pi* 10, e14, 2022, doi:[10.1017/fmp.2021.15](https://doi.org/10.1017/fmp.2021.15); read in arXiv:1502.04573v5 ([arXiv](https://arxiv.org/abs/1502.04573v5)), whose numbering is used: Theorem 5, restated with its proof in the subsection "Undecidability of the g.s. energy density", the energy bounds stated just before that restatement, and the section on periodic boundary conditions.
