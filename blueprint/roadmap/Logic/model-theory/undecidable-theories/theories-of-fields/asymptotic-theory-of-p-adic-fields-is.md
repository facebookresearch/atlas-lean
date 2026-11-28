# The asymptotic theory of p-adic fields with a cross-section is undecidable

For a fixed prime $p$, the set of sentences of the language of valued fields with a cross-section that hold in all but finitely many finite extensions of $\mathbb{Q}_p$ is undecidable, already for existential-universal sentences, although each single finite extension, with a suitable cross-section, is decidable in that language.

**Language.** $L_{\mathrm{val}}$ is the three-sorted language of valued fields: a field sort and a residue field sort, each with the language of rings $\{0,1,+,\cdot\}$, a value group sort with $\{0,+,<\}$ and a constant $\infty$, and function symbols for the valuation $v$ and the residue map. $L_{\mathrm{val},\times}$ adds a symbol for a *cross-section*, a group homomorphism $s : \Gamma \to K^\times$ with $v \circ s = \mathrm{id}_\Gamma$ (extended by $s(\infty) = 0$). Each finite extension $K$ of $\mathbb{Q}_p$ is viewed as an $L_{\mathrm{val},\times}$-structure with its normalized valuation and a cross-section $s_K$, which exists and corresponds to a choice of uniformizer; the source fixes an arbitrary such choice for each $K$ (Convention 2.2.6), and the result holds for any fixed choice.

**Asymptotic theory.** For a class $\mathcal{C}$ of structures, the *asymptotic theory* of $\mathcal{C}$ is the set of sentences true in all but finitely many members of $\mathcal{C}$ (up to isomorphism).

**Theorem (Kartas).** Fix a prime $p$. The asymptotic $L_{\mathrm{val},\times}$-theory of $\{K : [K : \mathbb{Q}_p] < \infty\}$ is undecidable (Theorem A). More precisely, its restriction to $\exists\forall$-sentences is already undecidable (the restatement of Theorem A in Section 4.3), and so is the asymptotic $\exists\forall$-theory of the totally ramified extensions $\{K : [K:\mathbb{Q}_p] = e(K/\mathbb{Q}_p) < \infty\}$ (Section 4.2).

By contrast, by Ax–Kochen and Ershov each finite extension of $\mathbb{Q}_p$, with a suitable cross-section, has a decidable $L_{\mathrm{val},\times}$-theory.

## Depends on

- [Field](../../../../Algebra/rings-and-fields/field.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Highly ramified extensions approximate $\mathbb{F}_p((t))$ in the sense of Krasner, Kazhdan and Deligne: for $K/\mathbb{Q}_p$ totally ramified of degree $e$, $\mathcal{O}_K/(p) \cong \mathbb{F}_p[t]/(t^e)$. The proof (1) interprets the asymptotic existential theory of the truncated polynomial rings $\{\mathbb{F}_p[t]/(t^n) : n \in \mathbb{N}\}$, with a predicate for the powers of $t$, in the asymptotic $\exists\forall$-theory of the totally ramified extensions; (2) interprets truncations of $(\mathbb{N}; 0, 1, +, \mid_p)$, where $m \mid_p n$ iff $n = p^s m$ for some $s$, in those rings; and (3) shows that the asymptotic existential theory of the truncations is undecidable, using Pheidas' theorem that the Diophantine problem of $(\mathbb{N}; 0, 1, +, \mid_p)$ is undecidable, itself based on the negative solution of Hilbert's tenth problem. Finally, adding the hypothesis "the residue field is $\mathbb{F}_p$" reduces the totally ramified case to all finite extensions. This adapts Pheidas' proof that $\mathbb{F}_p((t))$ is undecidable in $L_{\mathrm{val},\times}$. Whether the theory of all finite extensions of $\mathbb{Q}_p$ is decidable in the language of rings remains open.

## Sources

- Konstantinos Kartas, "An undecidability result for the asymptotic theory of p-adic fields", *Annals of Pure and Applied Logic* 174(2):103203, 2023, doi:10.1016/j.apal.2022.103203; read as arXiv:2105.03771v4, <https://arxiv.org/abs/2105.03771v4>: Theorem A of the introduction, Section 1.3 (languages and cross-sections), Section 3.3 (undecidability of fragments) and Sections 4.1–4.3 (the restated Theorem A for $\exists\forall$-sentences) of arXiv:2105.03771v4.
