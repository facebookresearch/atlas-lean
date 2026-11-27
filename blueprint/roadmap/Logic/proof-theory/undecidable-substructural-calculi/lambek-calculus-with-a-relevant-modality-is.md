# The Lambek calculus with a relevant modality is undecidable

Derivability in the Lambek calculus extended by a modality that allows contraction and permutation but not weakening is undecidable, already in the fragment with one division, which answers a question of Morrill and Valentín.

**Theorem (Kanovich, Kuznetsov and Scedrov).** The derivability problem for the [Lambek calculus with a relevant modality](lambek-calculus-with-a-relevant-modality.md) ${!}\mathbf{L}^*$ is undecidable. Moreover, it is undecidable already for the fragment ${!}\mathbf{L}^*_{/}$ with only the right division $/$ and ${!}$.

Since ${!}\mathbf{L}^*$ is a conservative fragment of Morrill and Valentín's calculus $\mathbf{Db}{!}{?}$, that calculus is undecidable too. In contrast, the source shows that when ${!}$ may be applied only to variables the problem is in NP (Theorem 6 there), and remarks that allowing ${!}$ on formulas of the form $r / (p / q)$ already gives undecidability.

## Depends on

- [Lambek calculus with a relevant modality](lambek-calculus-with-a-relevant-modality.md)

## Proof depends on

None.

## Expansion

The proof goes through extensions $\mathbf{L}^* + \mathcal{R}$ of the Lambek calculus by finitely many *Buszkowski rules* of the forms $\Pi_1 \to p,\ \Pi_2 \to q \,/\, \Pi_1, \Pi_2 \to r$ and $\Pi, q \to p \,/\, \Pi \to r$ for fixed primitive types $p, q, r$. Adapting Buszkowski's construction to empty antecedents, every recursively enumerable language without the empty word is described by such a calculus, so some finite $\mathcal{R}_0$ gives an undecidable $\mathbf{L}^* + \mathcal{R}_0$, even without $\backslash$ (Theorem 4). Each rule is turned into a formula $(r / q) / p$ or $r / (p / q)$; with $\mathcal{G}_\mathcal{R}$ the set of these formulas, $\mathbf{L}^* + \mathcal{R} \vdash \Pi \to A$ iff ${!}\mathbf{L}^* \vdash {!}B_1, \dots, {!}B_n, \Pi \to A$ for some $\{B_1, \dots, B_n\} \subseteq \mathcal{G}_\mathcal{R}$ (Theorem 5). Because $\mathcal{G}_\mathcal{R}$ is finite, a decision procedure for ${!}\mathbf{L}^*$ would decide $\mathbf{L}^* + \mathcal{R}_0$.

## Sources

- M. Kanovich, S. Kuznetsov and A. Scedrov, "Undecidability of the Lambek calculus with a relevant modality", in *Formal Grammar 2015/2016*, Lecture Notes in Computer Science 9804, Springer, 2016, pp. 240–256, doi:10.1007/978-3-662-53042-9_14; read as arXiv:1601.06303v4, <https://arxiv.org/abs/1601.06303v4>: Theorem 1 of arXiv:1601.06303v4, proved in Section 4 through Theorems 3–5.
