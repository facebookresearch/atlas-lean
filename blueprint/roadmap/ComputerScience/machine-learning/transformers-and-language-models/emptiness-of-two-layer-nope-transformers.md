# Emptiness of two-layer transformers without positional encodings is undecidable

Given an average-hard-attention transformer with only uniform attention layers, or a softmax attention transformer, with two attention layers and neither positional encodings nor masking, it is undecidable whether it accepts some word.

**Setting (Sälzer, Köcher, Kozachinskiy, Zetzsche and Lin).** Over an alphabet $\Sigma$ extended by an end marker $\triangleleft$, a *transformer* with $\ell$ layers consists of an input embedding $\iota : \Sigma \cup \{\triangleleft\} \to \mathbb{Q}^{d_1}$, a positional encoding $p$, and attention layers $\lambda_1, \dots, \lambda_\ell$. An attention layer is given by affine maps $Q$, $K$, $V$ and a ReLU network $N$, all with rational coefficients, weights and biases (as in the source, so that a transformer is a finite object), and maps $\vec{x}_1, \dots, \vec{x}_n$ to $\vec{y}_i = N(\vec{x}_i, \vec{a}_i)$ with $\vec{a}_i = \sum_j w(j) V\vec{x}_j$, where $w$ normalizes the scores $\langle K\vec{x}_i, Q\vec{x}_j \rangle$ either by softmax or by *averaging hard attention*, which gives weight $1/|P|$ to each of the $|P|$ maximal scores and $0$ to the others; no masking is applied. A layer is *uniform* if $K$ and $Q$ vanish, so that it averages over all positions. On $w = a_1 \cdots a_n$ the transformer runs its layers on $\iota(a_1) + p(n+1, 1), \dots, \iota(a_n) + p(n+1, n), \iota(\triangleleft) + p(n+1, n)$ and accepts $w$ if the first coordinate of the $n$-th output vector is positive. It has *no positional encoding* (NoPE) if $p$ is constant. $\mathrm{SMAT}$ denotes transformers with softmax layers only, and $\mathrm{NoPE}$-$\mathrm{AHAT}[\mathrm{U}]$ transformers with no positional encoding and uniform averaging-hard-attention layers only.

**Theorem (Sälzer, Köcher, Kozachinskiy, Zetzsche and Lin).** Given a transformer in $\mathrm{NoPE}$-$\mathrm{AHAT}[\mathrm{U}]$ or in $\mathrm{SMAT}$, already with two attention layers, it is undecidable whether its language is empty.

The same paper proves that every recursively enumerable counting property is a projection of a language recognized by such a transformer with two attention layers, that this fails with one layer, and that $\mathrm{NoPE}$-$\mathrm{AHAT}[\mathrm{U}]$ recognizes exactly the semialgebraic counting properties.

## Depends on

- [Transformer layers, numeric regimes and decoding conventions](transformer-layers-numeric-regimes-and-decoding-conventions.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

For every polynomial $p \in \mathbb{Z}[X_1, \dots, X_m]$, the authors construct effectively a $\mathrm{NoPE}$-$\mathrm{AHAT}[\mathrm{U}]$ transformer, which is also a softmax transformer, recognizing the words over $\{a_1, \dots, a_m\}$ whose letter counts are a zero of $p$; uniform layers compute the letter frequencies, and a fine-grained analysis shows that two layers suffice for the quadratic polynomials to which every Diophantine equation reduces. Its language is nonempty exactly when $p$ has a zero in $\mathbb{N}^m$, which is undecidable by the Davis–Putnam–Robinson–Matiyasevich theorem applied to a listable undecidable set. A good expansion links a page for the reduction of Diophantine equations to quadratic ones and for the halting problem used with the Davis–Putnam–Robinson–Matiyasevich theorem.

## Sources

- Marco Sälzer, Chris Köcher, Alexander Kozachinskiy, Georg Zetzsche and Anthony W. Lin, *The Counting Power of Transformers*, The Fourteenth International Conference on Learning Representations (ICLR 2026), 2026, https://proceedings.iclr.cc/paper_files/paper/2026/hash/2d663ddbad415a8105473a9e7f048da1-Abstract-Conference.html; the definitions of Section 2 and Theorem 1.4 with its proof in the appendix on universality and undecidability, read in arXiv:2505.11199v3.
