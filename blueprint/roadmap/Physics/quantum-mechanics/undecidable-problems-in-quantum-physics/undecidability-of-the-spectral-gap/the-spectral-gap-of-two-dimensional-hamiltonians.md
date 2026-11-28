# The spectral gap of two-dimensional translation-invariant Hamiltonians is undecidable

No algorithm decides, for translation-invariant nearest-neighbor Hamiltonians on the square lattice with fixed local dimension and algebraic entries, whether they are gapped or gapless, even under the promise that one of the two holds.

**Theorem (Cubitt, Perez-Garcia and Wolf).** Fix a universal Turing machine. One can construct explicitly a dimension $d$, $d^2\times d^2$ matrices $A,A',B,C,D,D'$, a $d\times d$ diagonal projector $\Pi$ and a rational number $\beta>0$, which can be chosen as small as desired, such that

1. $A$ and $D$ are diagonal with entries in $\mathbb Z$, $A'$ is Hermitian with entries in $\mathbb Z+\tfrac1{\sqrt2}\mathbb Z$, $B$ and $C$ have integer entries, and $D'$ is Hermitian with entries in $\mathbb Z$;
2. for each $n\in\mathbb N$, with $\varphi=\varphi(n)$ the rational number whose binary expansion lists the digits of $n$ in reverse order after the binary point and $|\varphi|$ the length of that expansion, the [translation-invariant nearest-neighbor Hamiltonian](translation-invariant-lattice-hamiltonians.md) on the square lattice with open boundary conditions given by

$$
h_1(n)=\alpha(n)\Pi,\qquad h_{\mathrm{col}}=D+\beta D',
$$

$$
h_{\mathrm{row}}(n)=A+\beta\bigl(A'+e^{i\pi\varphi}B+e^{-i\pi\varphi}B^\dagger+e^{i\pi2^{-|\varphi|}}C+e^{-i\pi2^{-|\varphi|}}C^\dagger\bigr),
$$

where $\alpha(n)\le\beta$ is an algebraic number computable from $n$, has local interaction strength at most $1$; and

3. if the universal machine halts on input $n$, the family $\{H^{\Lambda(L)}(n)\}_L$ is [gapped](gapped-and-gapless-families-of-hamiltonians.md) with spectral gap at least $1$, and if it does not halt on input $n$, the family is gapless.

Consequently the *spectral gap problem*, deciding of such a family whether it is gapped or gapless, is undecidable, already for one fixed local dimension $d$ and with the input $n$ entering only through the phases $e^{\pm i\pi\varphi}$, $e^{\pm i\pi2^{-|\varphi|}}$ and the on-site weight $\alpha(n)$.

Since $\beta$ can be arbitrarily small, the interactions are arbitrarily small quantum perturbations of the classical Hamiltonian with $h_{\mathrm{row}}=A$ and $h_{\mathrm{col}}=D$. In the gapped case the gap is at least the local interaction strength, and the result extends to periodic boundary conditions. The source also derives that, for any consistent formal system with a recursive set of axioms, some such Hamiltonian has neither its gap nor its gaplessness provable (Corollary 4).

## Depends on

- [Translation-invariant nearest-neighbor lattice Hamiltonians](translation-invariant-lattice-hamiltonians.md)
- [Gapped and gapless families of lattice Hamiltonians](gapped-and-gapless-families-of-hamiltonians.md)
- [Hypercubic lattice $\mathbb{Z}^d$](../../../../GraphTheory/graph-families-and-operations/hypercubic-lattice-graphs/hypercubic-lattice.md)
- [Halting of a code on an input](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/halts.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [Whether the ground-state energy density is zero is undecidable](ground-state-energy-density-is-undecidable.md)

## Expansion

The proof has four steps. First, a family of quantum Turing machines with fixed alphabet and state set uses quantum phase estimation to write the binary expansion of $n$ on the tape from the phase $\varphi(n)$ in the interactions, and then runs the universal machine on it. Second, following the translation-invariant history-state construction of Gottesman and Irani (after Feynman and Kitaev), this machine is encoded into a one-dimensional translation-invariant Hamiltonian whose ground-state energy on a chain of length $L$ is $0$ if the machine does not halt within the space and time available and is positive, though small, if it does. Third, these chains are placed on the segments of all scales of Robinson's aperiodic tiling of the plane, enforced by a classical tiling Hamiltonian, which amplifies the energy difference: the ground-state energy density becomes $0$ in the non-halting case and positive in the halting case. Fourth, this Hamiltonian is combined with a trivial Hamiltonian of ground-state energy $0$ and gap $1$ and a critical Hamiltonian whose spectrum becomes dense in $[0,\infty)$, and the decisive input is the finite-size promise of Corollary 54, not the energy density alone: in the halting case $\lambda_0(H_u^{\Lambda(L)})\ge1$ for all $L\ge L(n)$, so the combined Hamiltonian is at least the trivial one and its unique product ground state with gap $1$ remains, giving a gapped family; in the non-halting case $\lambda_0(H_u^{\Lambda(L)})\le0$ for all $L$, so the dense spectrum of the critical Hamiltonian appears above the ground energy, giving a gapless family (Section 6.2). Zero energy density alone would not decide this, since $\lambda_0=L$ for every $L$ also has density $0$. Quantum phase estimation, used in the first step, is reached through the ground-state energy density page listed above. That page's statement gives only the dichotomy of the energy density; a good expansion links a page for the finite-size bounds of Proposition 53 and Corollary 54, on which the fourth step rests. A good expansion also links pages for the properties of Robinson's tiling, the history-state (Feynman–Kitaev) construction, the Gottesman–Irani translation-invariant clock, well-formed quantum Turing machines (Bernstein and Vazirani), and the phase-estimation quantum Turing machine that carries out the readout on the tape.

## Sources

- T. Cubitt, D. Perez-Garcia and M. M. Wolf, "Undecidability of the spectral gap", *Forum of Mathematics, Pi* 10, e14, 2022, doi:[10.1017/fmp.2021.15](https://doi.org/10.1017/fmp.2021.15); read in arXiv:1502.04573v5 ([arXiv](https://arxiv.org/abs/1502.04573v5)), whose numbering is used: Theorem 3 and the comments after it, Corollary 4, Section 1.4, "Brief overview of the proof", Theorem 32 (local Hamiltonian encoding of quantum Turing machines), Theorem 10 (phase-estimation quantum Turing machine), Proposition 53, Corollary 54 and Section 6.2 (the gapped and gapless cases), and Section 6.3, "Periodic boundary conditions".
