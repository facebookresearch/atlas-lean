# The spectral gap of one-dimensional translation-invariant Hamiltonians is undecidable

No algorithm decides, for translation-invariant nearest-neighbor Hamiltonians on a spin chain with fixed local dimension, built from matrices over Q(√2) and phases determined by the input, whether they are gapped or gapless, even under the promise that one of the two holds.

**Theorem (Bausch, Cubitt, Lucia and Perez-Garcia).** Fix a universal Turing machine. There are explicitly constructible nearest-neighbor interactions $h^{(2)}(n)$ and on-site terms $h^{(1)}(n)$, parametrized by $n\in\mathbb N$, with $\|h^{(1)}(n)\|\le2$ and $\|h^{(2)}(n)\|\le1$, such that the family of [translation-invariant chain Hamiltonians](translation-invariant-lattice-hamiltonians.md) with open boundary conditions and fixed local dimension $d$

$$
H_N(n)=\sum_{i=1}^{N-1}h^{(2)}_{i,i+1}(n)+\sum_{i=1}^{N}h^{(1)}_i(n),\qquad N\ge1,
$$

satisfies:

1. if the universal machine halts on input $n$, then $\{H_N(n)\}_N$ is [gapless](gapped-and-gapless-families-of-hamiltonians.md);
2. if it does not halt on input $n$, then $\{H_N(n)\}_N$ is gapped, and moreover $\Delta(H_N(n))\ge1$ for all $N\ge1$.

The interactions can be chosen of the form

$$
h^{(1)}(n)=a+\beta\bigl(2^{-2|n|}a'+a''\bigr),
$$

$$
h^{(2)}(n)=b+\beta\bigl(2^{-2|n|}b'+b''+e^{i\pi\phi(n)}b'''+e^{-i\pi\phi(n)}b'''^\dagger+e^{i\pi2^{-2|n|}}b''''+e^{-i\pi2^{-2|n|}}b''''^\dagger\bigr),
$$

where $0<\beta\le1$ is any rational number, $|n|$ is the number of binary digits $n_1n_2\cdots n_{|n|}$ of $n$, $\phi(n)=0.n_11n_21\cdots n_{|n|-1}1n_{|n|}$ is its binary fraction with interleaved $1$s, $a,a',a''$ are $d\times d$ and $b,\dots,b''''$ are $d^2\times d^2$ matrices, $a$ and $b$ are diagonal with integer entries, $a',a'',b',b''$ are Hermitian with entries in $\mathbb Q[\sqrt2]$, and $b''',b''''$ have rational entries. Hence the spectral gap problem for such chains is undecidable.

Compared with the two-dimensional result, the roles of halting are swapped: here the halting instances are the gapless ones. Since $\beta$ is arbitrarily small, the chains are arbitrarily small perturbations of classical chains. With periodic boundary conditions the result holds for chain lengths coprime to a fixed $P$, at the cost of a local dimension growing with $P$.

## Depends on

- [Translation-invariant nearest-neighbor lattice Hamiltonians](translation-invariant-lattice-hamiltonians.md)
- [Gapped and gapless families of lattice Hamiltonians](gapped-and-gapless-families-of-hamiltonians.md)
- [Halting of a code on an input](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/halts.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [Quantum phase estimation](../../../../ComputerScience/quantum-algorithms/quantum-phase-estimation.md)

## Expansion

In one dimension the Robinson tiling used in two dimensions is unavailable, so the proof introduces a *marker Hamiltonian* whose ground state partitions the chain periodically into segments, with a segment length that the ground-state energy can tune. On each segment a translation-invariant history-state Hamiltonian, in the style of Gottesman and Irani, runs a phase-estimation quantum Turing machine that reads $n$ from the phase $\phi(n)$ and then the universal machine. A segment too short for the machine to halt is penalized when the head runs into the next marker, and every segment earns a small bonus that shrinks with its length and is smaller than any such penalty. If the machine halts, the cheapest configuration is a periodic arrangement of segments just long enough for it to halt, and the bonuses drive the ground-state energy of this part to $-\infty$ as the chain grows; if it does not halt, a single segment is best and, after a constant energy shift, the spectrum of this part stays at or above $1$. This part is combined, through a direct sum with a guard term, with a dense Hamiltonian whose spectrum fills $[0,\infty)$ and with a trivial Hamiltonian of ground-state energy $0$ and gap $1$: in the halting case the dense spectrum sits above a diverging ground-state energy and the family is gapless, and in the non-halting case the trivial ground state with gap at least $1$ remains. Quantum phase estimation is linked above; a good expansion also links pages for the history-state construction with the Gottesman–Irani clock, well-formed quantum Turing machines, the phase-estimation quantum Turing machine of Theorem 14 that performs the readout on a segment, and the marker Hamiltonian.

## Sources

- J. Bausch, T. S. Cubitt, A. Lucia and D. Perez-Garcia, "Undecidability of the spectral gap in one dimension", *Physical Review X* 10(3), 031038, 2020, doi:[10.1103/PhysRevX.10.031038](https://doi.org/10.1103/PhysRevX.10.031038); read in arXiv:1810.01858v2 ([arXiv](https://arxiv.org/abs/1810.01858v2)), whose numbering is used: Theorem 1 (main result), its restatement as Theorem 26 with Theorem 25 (spectrum of the combined Hamiltonian), the marker Hamiltonian of Theorem 11, the phase-estimation machine of Theorem 14, and Lemma 27 in Section VIII.A, "Periodic Boundary Conditions".
