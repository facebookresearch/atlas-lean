# Emptiness of two-layer transformers without positional encodings is undecidable

Given an average-hard-attention transformer with only uniform attention layers, or a softmax attention transformer, with two attention layers and neither positional encodings nor masking, it is undecidable whether it accepts some word.

**Setting (Sälzer, Köcher, Kozachinskiy, Zetzsche and Lin).** Over an alphabet $\Sigma$ extended by an end marker $\triangleleft$, a *transformer* with $\ell$ layers consists of an input embedding $\iota : \Sigma \cup \{\triangleleft\} \to \mathbb{Q}^{d_1}$, a positional encoding $p$, and attention layers $\lambda_1, \dots, \lambda_\ell$. An attention layer is given by affine maps $Q$, $K$, $V$ and a ReLU network $N$, all with rational coefficients, weights and biases (as in the source, so that a transformer is a finite object), and maps $\vec{x}_1, \dots, \vec{x}_n$ to $\vec{y}_i = N(\vec{x}_i, \vec{a}_i)$ with $\vec{a}_i = \sum_j w(j) V\vec{x}_j$, where $w$ normalizes the scores $\langle K\vec{x}_i, Q\vec{x}_j \rangle$ either by softmax or by *averaging hard attention*, which gives weight $1/|P|$ to each of the $|P|$ maximal scores and $0$ to the others; no masking is applied. A layer is *uniform* if $K$ and $Q$ vanish, so that it averages over all positions. On $w = a_1 \cdots a_n$ the transformer runs its layers on $\iota(a_1) + p(n+1, 1), \dots, \iota(a_n) + p(n+1, n), \iota(\triangleleft) + p(n+1, n)$ and accepts $w$ if the first coordinate of the $(n+1)$-th output vector, at the end marker, is positive; this also covers the empty word. Section 2.1 of the source prints $y_n[1]$, but its informal description checks "the last vector" and its proofs read the output at the end marker (in the proof of Theorem B.2 the output on $w\triangleleft$ is $N(\iota(\triangleleft), \dots)$); without positional encoding the output at position $n$ would also depend on the last letter. It has *no positional encoding* (NoPE) if $p$ is constant, a fixed rational vector. $\mathrm{SMAT}$ denotes transformers with softmax layers only, $\mathrm{NoPE}$-$\mathrm{SMAT}$ those of them whose positional encoding is a constant rational vector, and $\mathrm{NoPE}$-$\mathrm{AHAT}[\mathrm{U}]$ transformers with no positional encoding and uniform averaging-hard-attention layers only.

**Theorem (Sälzer, Köcher, Kozachinskiy, Zetzsche and Lin).** Given a transformer in $\mathrm{NoPE}$-$\mathrm{AHAT}[\mathrm{U}]$ or in $\mathrm{NoPE}$-$\mathrm{SMAT}$, already with two attention layers, it is undecidable whether its language is empty.

The same paper proves that every recursively enumerable counting property is a projection of a language recognized by such a transformer with two attention layers, that this fails for $\mathrm{NoPE}$-$\mathrm{AHAT}[\mathrm{U}]$ with one attention layer (Theorem B.2: one-layer NoPE-AHAT recognize exactly the quantifier-free Presburger properties), while the one-layer softmax case is left open, and that $\mathrm{NoPE}$-$\mathrm{AHAT}[\mathrm{U}]$ recognizes exactly the semialgebraic counting properties.

## Depends on

- [Transformer layers, numeric regimes and decoding conventions](transformer-layers-numeric-regimes-and-decoding-conventions.md)
- [Softmax](../attention-and-low-rank-adaptation/softmax-attention-basics/softmax.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [The halting problem is undecidable by multi-stack machines](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halting.md)

## Expansion

For every polynomial $p \in \mathbb{Z}[X_1, \dots, X_m]$, the authors construct effectively a $\mathrm{NoPE}$-$\mathrm{AHAT}[\mathrm{U}]$ transformer, which is also a softmax transformer, recognizing the words over $\{a_1, \dots, a_m\}$ whose letter counts are a zero of $p$; uniform layers compute the letter frequencies, and two layers suffice for a system of quadratic polynomials. A polynomial $p$ is replaced by quadratic polynomials $q_1, \dots, q_r$ over $m + k$ variables, one fresh variable per multiplication in $p$, so that $p(x) = 0$ iff $q_1(x, y) = \dots = q_r(x, y) = 0$ for some $y \in \mathbb{N}^k$; the transformer recognizes the words over the extended alphabet $\{a_1, \dots, a_{m+k}\}$ whose letter counts solve the system, and the words for $p$ are their projection to $\{a_1, \dots, a_m\}$ (Appendix B). The projection preserves nonemptiness, not the language, so the transformer's language is nonempty exactly when $p$ has a zero in $\mathbb{N}^m$, which is undecidable by the Davis–Putnam–Robinson–Matiyasevich theorem applied to the halting set. A good expansion links a page for the reduction of a polynomial equation to a system of quadratic ones.

## Sources

- Marco Sälzer, Chris Köcher, Alexander Kozachinskiy, Georg Zetzsche and Anthony W. Lin, *The Counting Power of Transformers*, The Fourteenth International Conference on Learning Representations (ICLR 2026), 2026, https://proceedings.iclr.cc/paper_files/paper/2026/hash/2d663ddbad415a8105473a9e7f048da1-Abstract-Conference.html; the definitions of Section 2 and Theorem 1.4 with its proof in the appendix on universality and undecidability, and Theorem B.2 in Appendix B, read in arXiv:2505.11199v3.
