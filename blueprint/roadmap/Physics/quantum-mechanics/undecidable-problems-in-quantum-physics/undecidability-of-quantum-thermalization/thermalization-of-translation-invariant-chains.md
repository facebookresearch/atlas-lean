# Relaxation and thermalization of one-dimensional translation-invariant quantum chains are undecidable

For a fixed product initial state and a fixed single-site observable, no algorithm decides, from a shift-invariant nearest-neighbor Hamiltonian on a chain, whether the long-time average of the observable in the thermodynamic limit is close to a given value, or to its thermal equilibrium value.

**Setting.** Consider a chain of $L$ sites with periodic boundary conditions, each carrying a $d$-dimensional Hilbert space $\mathcal{H}$, where $d\ge d_0$ for relaxation and $d\ge d_0+5$ for thermalization, $d_0$ being a fixed number that the source constructs. A *shift-invariant nearest-neighbor Hamiltonian* is $H = \sum_i h_{i,i+1}$, determined by one $d^2 \times d^2$ Hermitian matrix $h$. Fix two orthogonal single-site states $|\phi_0\rangle, |\phi_1\rangle$, the initial state $|\psi_0^L\rangle = |\phi_0\rangle \otimes |\phi_1\rangle \otimes \cdots \otimes |\phi_1\rangle$, and the observable $\mathcal{A}_L = \frac{1}{L}\sum_{i=1}^{L} A_i$ for a single-site operator $A$. With $|\psi(t)\rangle$ the state evolved by $H$ from $|\psi_0^L\rangle$, define the long-time average and its thermodynamic limit (time limit first)

$$
\overline{A}_L = \lim_{T \to \infty} \frac{1}{T} \int_0^T \langle \psi(t) | \mathcal{A}_L | \psi(t) \rangle \, dt, \qquad \overline{A} = \lim_{L \to \infty} \overline{A}_L ,
$$

and the equilibrium value $\mathcal{A}^{\mathrm{MC}} = \lim_{L\to\infty} \operatorname{Tr}[\mathcal{A}_L \rho^{\mathrm{MC}}_L]$ with $\rho^{\mathrm{MC}}_L$ the microcanonical state at the energy $\langle\psi_0^L|H|\psi_0^L\rangle$ of the initial state.

**Theorem (Shiraishi–Matsumoto).**

1. *Relaxation.* Fix a local dimension $d\ge d_0$. Let $|\phi_0\rangle, |\phi_1\rangle$ and $A$ be given, with some state $|\phi_2\rangle$ orthogonal to both such that $\langle \phi_2 | A | \phi_2 \rangle \ne \langle \phi_1 | A | \phi_1 \rangle$, and fix $M > 1$, which may be arbitrarily large. Then there are errors $0 < \varepsilon_1 < \varepsilon_2 = M \varepsilon_1$ and a value $A^*$ such that, under the promise that either $|\overline{A} - A^*| < \varepsilon_1$ or $|\overline{A} - A^*| > \varepsilon_2$, deciding which holds for a given shift-invariant nearest-neighbor Hamiltonian $H$ is undecidable (Theorem 1 of the source).
2. *Thermalization.* Fix a local dimension $d\ge d_0+5$. Under the analogous hypotheses, with states $|\phi_2\rangle, |\phi_3\rangle$ orthogonal to $|\phi_0\rangle, |\phi_1\rangle, A|\phi_0\rangle, A|\phi_1\rangle$ whose expectation values of $A$ lie above and below the range of $A$ on the span of $|\phi_0\rangle, |\phi_1\rangle$, and for every fixed $M > 1$, there are errors $0 < \varepsilon_1 < \varepsilon_2 = M \varepsilon_1$ such that, under the promise that either $|\overline{A} - \mathcal{A}^{\mathrm{MC}}| < \varepsilon_1$ or $|\overline{A} - \mathcal{A}^{\mathrm{MC}}| > \varepsilon_2$, deciding which holds for a given $H$ is undecidable (Theorem 2).

The input is the Hamiltonian alone; the initial state and the observable are fixed. The condition $\varepsilon_1 < \varepsilon_2$, that is $M > 1$, keeps the two alternatives of each promise disjoint; the source states it in the setup before Theorem 1 and notes that the ratio $M$ can be arbitrarily large. The number $d_0$ is fixed by the construction; the Supplementary Note estimates $d_0\simeq120$ (its Section 10.5).

## Depends on

- [Expectation value of an observable](../../postulates-of-finite-dimensional-quantum-mechani/expectation-value.md)
- [Density matrices, pure states and reduced states](../../../../QuantumInformation/quantum-states-distances-and-entropy/density-matrices-and-fidelity/density-matrices-and-reduced-states.md)
- [Polynomial-time reduction between promise problems](../../../../TheoryOfComputation/randomized-and-quantum-complexity/local-hamiltonian-problem/promise-reduces.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The proof reduces the halting problem of a fixed universal reversible Turing machine. The key lemma of the source gives, for a basis $\{|e_i\rangle\}$ of the site with $\langle e_1 | A | e_1 \rangle = 0 < \langle e_2 | A | e_2 \rangle$ and any $\eta > 0$, a shift-invariant nearest-neighbor Hamiltonian $H$ and local unitaries $V_u$ fixing $|e_0\rangle$, one for each input $u$ of the machine, such that from the initial state $(V_u|e_0\rangle) \otimes (V_u|e_1\rangle)^{\otimes (L-1)}$ the thermodynamic long-time averages of both $A$ and $V_uAV_u^\dagger$ under $H$ are at least $(\tfrac14 - \eta)\langle e_2 | A | e_2 \rangle$ if the machine halts on $u$ and at most $\eta$ if it does not (Lemma 1 of the Supplementary Note, eqs. (S.9)–(S.10)). With $V=V_u^{\otimes L}$, the long-time average of $A$ under $V^\dagger HV$ from $|\psi_0^L\rangle$ equals that of $V_uAV_u^\dagger$ under $H$ from $V|\psi_0^L\rangle$, so the second bound, not the first, gives Theorem 1 for the Hamiltonians $V^\dagger HV$, which carry the dependence on $u$ while the initial state and the observable stay fixed (eqs. (S.15)–(S.17)). The lemma is proved by first building a classical machine that simulates the universal reversible machine and changes the value of $A$ according to whether it halts, and then a quantum many-body system emulating that machine. The thermalization statement follows by choosing the basis so that the value reached in the halting case equals the microcanonical value at the energy of the initial state (Section 11.3 of the Supplementary Note). A good expansion links pages for the existence of a universal reversible Turing machine (see Morita's monograph on reversible computing, cited by the source) and for the lemma with its construction.

## Sources

- N. Shiraishi and K. Matsumoto, "Undecidability in quantum thermalization", Nature Communications 12 (2021), article 5084, https://doi.org/10.1038/s41467-021-25053-0; read in arXiv:2012.13889v2 (Theorems 1 and 2 and the setup preceding them, including the condition $0 < \varepsilon_1 < \varepsilon_2$, and the Lemma and proof outline after them, of arXiv:2012.13889v2), together with the Supplementary Note published with the article, <https://static-content.springer.com/esm/art%3A10.1038%2Fs41467-021-25053-0/MediaObjects/41467_2021_25053_MOESM1_ESM.pdf>, whose numbering is used for the points it adds: Theorem 1b (the article's Theorem 1) and Theorem 2 with the bounds $d\ge d_0$ and $d\ge d_0+5$, Lemma 1 with eqs. (S.9)–(S.10), the microcanonical energy in Section 2, the proof of Theorem 1b in Section 5, eqs. (S.15)–(S.17), and Sections 10.5 and 11.3.
