# The capacity of finite-state channels is not Banach–Mazur computable, already with one bit of input, output and memory

As a function of the computable transition probabilities, the capacity of finite-state channels with binary input, output and state alphabets is not Banach–Mazur computable, the weakest notion of computability; so no algorithm computes it, and it has no computable converging lower and upper bounds.

Let finite-state channels in product form, $p(y, s \mid x, s') = p(y \mid x, s')\, q(s \mid x, s')$, and their capacity $C(\{p, q, s_0\})$ be as in [Finite-state channels and their capacity](finite-state-channels.md). A real number is *computable* if some algorithm produces rationals $r_n$ with $|x - r_n| < 2^{-n}$ for all $n$; let $\mathcal{P}_c, \mathcal{Q}_c$ be the sets of conditional distributions $p, q$ all of whose values are computable reals. A function on computable inputs is *Banach–Mazur computable* if it maps every computable sequence of computable inputs to a computable sequence of computable reals; every function computed by an algorithm acting on representations of its inputs (Borel computable) is Banach–Mazur computable.

**Theorem (Boche, Schaefer and Poor).** For all $|\mathcal{X}|, |\mathcal{Y}|, |\mathcal{S}| \ge 2$, the capacity function $C(\{p, q, s_0\}) : \mathcal{P}_c \times \mathcal{Q}_c \times \mathcal{S} \to \mathbb{R}$ is not Banach–Mazur computable (Theorem 19 of the source); in particular no algorithm computes the capacity from the channel parameters.

The source also shows that for some initial state $s_0$ there are no computable sequences $(F_N)$ and $(G_N)$ of computable continuous functions of $(p, q)$ with $F_N \le C(\{p, q, s_0\}) \le G_N$ and both converging pointwise to $C(\{p, q, s_0\})$ (Theorem 26). The capacity function is moreover discontinuous (Theorem 32), so it has no single-letter formula as the maximum of a continuous function over a fixed compact set (Theorem 33); for channels whose lower and upper capacities coincide the capacity of each computable channel is a computable real number (Theorem 29).

## Depends on

- [Finite-state channels and their capacity](finite-state-channels.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

For binary alphabets the proof takes a channel that is noiseless in state $0$ and a binary symmetric channel with crossover probability $\epsilon \in (0, 1/2)$ in state $1$, and state dynamics depending on a parameter, so that the capacity jumps according to whether a computable sequence of parameters is zero. Feeding in a recursively enumerable, non-recursive set $\mathcal{A} \subseteq \mathbb{N}$, whose existence is the undecidability of the halting problem, would give an algorithm deciding membership in $\mathcal{A}$ if the capacity were Banach–Mazur computable. Larger alphabets embed the binary case. Theorem 26 follows from Theorem 19 by Corollary 11 of the source: when an increasing and a decreasing computable sequence of computable continuous functions have a common limit, that limit is a computable continuous function, hence Banach–Mazur computable. These constructions have no pages.

## Sources

- H. Boche, R. F. Schaefer and H. V. Poor, "Shannon meets Turing: non-computability and non-approximability of the finite state channel capacity", Communications in Information and Systems 20 (2020), no. 2, 81–116, https://doi.org/10.4310/CIS.2020.v20.n2.a1; read in arXiv:2008.13270v2 (Section 2 on computable reals and functions, Corollary 11 and Theorems 19, 26, 29, 32 and 33 of arXiv:2008.13270v2, which numbers all statements in one sequence).
