# The spectral gap of rotationally symmetric plaquette Hamiltonians is undecidable

The spectral gap stays undecidable for translation-invariant Hamiltonians on the square lattice whose four-body plaquette interactions are also invariant under rotation by a quarter turn: rotational symmetry does not make the problem decidable.

**Lattice and symmetry.** Place sites at the midpoints of the edges of the unit cells of an $L\times L$ square of $\mathbb Z^2$, $L\ge1$, each carrying $\mathbb C^d$; four sites $(i,j,k,l)$, listed in a fixed cyclic order, form a *plaquette* when they lie on the four edges of one unit cell. A translation-invariant plaquette Hamiltonian is

$$
H^{\Lambda(L)}=\sum_{i\in\Lambda(L)}h^{(i)}+\sum_{(i,j,k,l)\in\Lambda(L)}h^{(i,j,k,l)},
$$

with the same on-site term $h^{(i)}$ and the same plaquette term $h^{(i,j,k,l)}$ at every site and plaquette. It is *invariant under rotations* if $h^{(i,j,k,l)}=U_{\pi/2}h^{(i,j,k,l)}U_{\pi/2}^\dagger$, where $U_{\pi/2}|x\rangle|y\rangle|w\rangle|z\rangle=|z\rangle|x\rangle|y\rangle|w\rangle$ permutes the four sites cyclically. Gapped and gapless are meant as for [lattice Hamiltonians](gapped-and-gapless-families-of-hamiltonians.md), with $L\to\infty$.

**Theorem (Castilla-Castellano and Lucia).** For any universal Turing machine one can construct a family $H(n)$, $n\in\mathbb N$, of two-dimensional translation-invariant Hamiltonians with four-body plaquette interactions that are invariant under rotations such that:

1. if the universal machine halts on input $n$, the family $\{H^{\Lambda(L)}(n)\}_L$ is gapped;
2. if it does not halt on input $n$, the family $\{H^{\Lambda(L)}(n)\}_L$ is gapless.

Hence deciding whether such a rotationally symmetric family is gapped or gapless is undecidable.

The interactions need not be invariant under reflections: the construction is chiral, and the source leaves reflection symmetry in two dimensions open. Along the way the source shows that deciding whether the ground-state energy density $\lim_{L\to\infty}\lambda_0(H^{\Lambda(L)})/(2L(L+1))$ is $0$ or positive is undecidable for these rotationally symmetric Hamiltonians, as in the [translation-invariant case](ground-state-energy-density-is-undecidable.md).

## Depends on

- [Gapped and gapless families of lattice Hamiltonians](gapped-and-gapless-families-of-hamiltonians.md)
- [Translation-invariant nearest-neighbor lattice Hamiltonians](translation-invariant-lattice-hamiltonians.md)
- [Hypercubic lattice $\mathbb{Z}^d$](../../../../GraphTheory/graph-families-and-operations/hypercubic-lattice-graphs/hypercubic-lattice.md)
- [Halting of a code on an input](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/halts.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [Quantum phase estimation](../../../../ComputerScience/quantum-algorithms/quantum-phase-estimation.md)

## Expansion

The proof follows the two-dimensional construction of Cubitt, Perez-Garcia and Wolf with symmetric ingredients. A one-dimensional, translation-invariant and reflection-invariant history-state Hamiltonian encodes a quantum Turing machine that first writes $n$ on its tape by quantum phase estimation (Section 3.1) and then runs the universal machine on input $n$, with a small energy penalty when the computation halts within the segment. A rotationally symmetric tile set, a variant of Robinson's aperiodic tiling, is encoded in plaquette interactions; its squares of side $4^m$ carry the one-dimensional computation along their edges, which gives energy bounds $\lambda_0\le-\tfrac34\beta L$ in the non-halting case and $\lambda_0\ge\beta(L^2\delta_2(n)-L\delta_1(n))$ with $\delta_2(n)>0$ in the halting case. Finally this Hamiltonian is combined with a rotationally symmetric trivial gapped Hamiltonian and with the spin-$\tfrac12$ ferromagnetic Heisenberg model written in plaquette form, which is gapless, so that the halting case is gapped and the non-halting case gapless. A good expansion links pages for the history-state construction with a translation-invariant clock, the rotationally symmetric Robinson-type tiling, and the gaplessness of the ferromagnetic Heisenberg model.

## Sources

- L. Castilla-Castellano and A. Lucia, "Undecidability of the spectral gap in rotationally symmetric Hamiltonians", *Physical Review Research* 8, 013033, 2026, doi:[10.1103/5lrn-h3cg](https://doi.org/10.1103/5lrn-h3cg); read in arXiv:2410.13589v2 ([arXiv](https://arxiv.org/abs/2410.13589v2)), whose numbering is used: Definitions 3 (rotational invariance) and 4 (energy density, gapped, gapless), the plaquette lattice of Section 2, the phase-estimation machine of Section 3.1, Proposition 24, Corollary 25 and Theorem 26 of Section 6, and Examples 5 and 6 (trivial and Heisenberg Hamiltonians).
