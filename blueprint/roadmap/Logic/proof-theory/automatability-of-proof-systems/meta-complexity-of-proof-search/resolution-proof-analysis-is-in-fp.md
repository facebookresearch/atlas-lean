# Arteche–Atserias–de Rezende–Khaniki: short Resolution proofs of Resolution lower bounds leak satisfying assignments

Given a satisfiable CNF $\varphi$ on $n$ variables and any Resolution refutation of $\mathrm{Ref}_s(\varphi)$ with $s\ge n^{3}$, a deterministic polynomial-time algorithm extracts a satisfying assignment of $\varphi$; for $s\ge n^{2}$ a zero-error randomized algorithm does.

1. $\mathrm{FPAP}_{\mathrm{Res}}[n^{3}]\in\mathsf{FP}$: there is a deterministic polynomial-time algorithm that, given $(\varphi,\pi,1^{s})$ with $s\ge n^{3}$ and $\pi$ a Resolution refutation of $\mathrm{Ref}_s(\varphi)$, outputs a satisfying assignment of $\varphi$ whenever $\varphi$ is satisfiable, and otherwise outputs $0$ as $\mathrm{FPAP}$ requires (it rejects if $\pi$ is not a correct refutation).
2. $\mathrm{FPAP}_{\mathrm{Res}}[n^{2}]\in\mathsf{FZPP}$.
3. Consequently there is a polynomial-time Levin reduction from search-3SAT to the Proof Size Problem for Resolution: $\varphi\mapsto\mathrm{Ref}_{n^{3}}(\varphi)$, with Pudlák's polynomial-size refutation built from a satisfying assignment in one direction and the extraction algorithm in the other.

The extraction argument is a feasibly constructive proof of the Atserias–Müller lower bound, formalizable in Cook's theory $\mathrm{PV}_1$; as a consequence, Extended Frege efficiently proves a formalization of the statement that automating Resolution is NP-hard.

## Expansion

First check that $\pi$ refutes $\mathrm{Ref}_s(\varphi)$. A greedy deterministic restriction disables $d\le(c/2)\sqrt{s\log|\pi|}$ blocks and reduces the block-width of $\pi$ to at most $c\sqrt{s\log|\pi|}$. The extraction algorithm then walks the restricted refutation and either finds a clause of block-width at least $(s-d-n)/3n$ or reads off a satisfying assignment of $\varphi$. In the first case $|\pi|>2^{\varepsilon s/n}\ge 2^{\varepsilon n^{2}}$, so brute force over all $2^{n}$ assignments is polynomial in the input length. With $s\ge n^{2}$ the randomized width reduction to $O(\log|\pi|)$ gives the same conclusion with zero error.

## Depends on

- [The Proof Analysis Problem PAP and analyzable proof systems](proof-analysis-problem.md)
- [Levin reductions (witness-preserving many-one reductions)](../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/cryptographic-meta-complexity/limits-of-np-hardness/levin-reductions.md)

## Proof depends on

- [Atserias–Müller: automating resolution is NP-hard](../atserias-muller.md)
- [The Atserias–Müller reduction from SAT to resolution proof size](../am-reduction-formula.md)

## Sources

- Noel Arteche, Albert Atserias, Susanna F. de Rezende and Erfan Khaniki, "The Proof Analysis Problem", *66th IEEE Symposium on Foundations of Computer Science (FOCS 2025)*, 2025, https://doi.org/10.1109/FOCS63196.2025.00133; numbering from arXiv:2506.16956v2 (Theorem 1.1, Lemmas 4.2, 4.3 and 4.5, Theorems 4.6 and 4.7, Corollary 4.8, Theorems 6.9 and 8.2).
