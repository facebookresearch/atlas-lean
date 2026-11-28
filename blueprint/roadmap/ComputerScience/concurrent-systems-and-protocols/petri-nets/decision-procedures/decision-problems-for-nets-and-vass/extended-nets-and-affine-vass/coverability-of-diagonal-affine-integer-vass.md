# Coverability for integer VASS with diagonal affine updates is undecidable in dimension four

Integer vector addition systems whose transitions apply affine maps with diagonal matrices to counters ranging over $\mathbb{Z}$ have an undecidable coverability problem already with four counters, and an undecidable reachability problem already with two.

**Setting (Haase and Halfon).** For a set $\mathfrak{A}$ of integer $d \times d$ matrices, a *$d$-dimensional integer register machine over $\mathfrak{A}$* is $\mathcal{A} = (Q, \Sigma, d, \Delta, \tau)$ with a finite set of control states $Q$, a finite alphabet $\Sigma$, transitions $\Delta \subseteq Q \times \Sigma \times Q$, and a map $\tau$ assigning to each letter $a$ an affine transformation $\tau(a)(\vec{v}) = A\vec{v} + \vec{b}$ with $A \in \mathfrak{A}$ and $\vec{b} \in \mathbb{Z}^d$. Configurations are pairs $q(\vec{v}) \in Q \times \mathbb{Z}^d$, and a transition $(q, a, q')$ leads from $q(\vec{v})$ to $q'(\tau(a)(\vec{v}))$; counters may take negative values. *Reachability* asks, given $\mathcal{A}$ and configurations $q(\vec{v})$, $q'(\vec{v}')$, whether $q(\vec{v})$ reaches $q'(\vec{v}')$; *coverability* asks whether $q(\vec{v})$ reaches $q'(\vec{z})$ for some $\vec{z} \in \mathbb{Z}^d$ with $\vec{z} \ge \vec{v}'$ componentwise. Let $\mathfrak{D}_d$ be the set of diagonal integer $d \times d$ matrices.

**Theorem (Haase and Halfon).**

1. Reachability for integer register machines over $\mathfrak{D}_2$ is undecidable.
2. Coverability for integer register machines over $\mathfrak{D}_d$ is undecidable already for $d = 4$.

Clause 1 is due to J. Reichert (PhD thesis, 2015); Haase and Halfon repeat his argument, and Blondin, Haase, Mazowiecki and Raskin present it in the proof of Proposition 6.3 of their refereed article, with the matrices $I$, $\mathrm{diag}(2, 1)$ and $\mathrm{diag}(1, 2)$, which are diagonal. Reachability over $\mathfrak{D}_1$ is decidable, and the source leaves coverability over $\mathfrak{D}_2$ and $\mathfrak{D}_3$ open.

## Depends on

- [Vector addition systems](../../../vector-addition-systems.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable over the binary alphabet](../../../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/not-tm2-decidable-pcp-bool.md)

## Expansion

Clause 1 reduces from the Post correspondence problem over $\{0, 1\}$. For an instance $u_1, \dots, u_n, v_1, \dots, v_n$, the machine loops at a state $q_0$ reading, for a chosen $i$, the word $u_i \tilde{v}_i$, where $\tilde{v}_i$ is $v_i$ over a marked copy of the alphabet. Reading $0$ maps $(x, y)$ to $(2x, y)$ and $1$ maps it to $(2x + 1, y)$, while $\tilde 0$ and $\tilde 1$ act in the same way on the second counter; starting from $(1, 1)$, which adds an artificial leading $1$ to both words as in the proof of Proposition 6.3 of Blondin, Haase, Mazowiecki and Raskin, the two counters hold the binary values of $1 u_{i_1} \cdots u_{i_p}$ and $1 v_{i_1} \cdots v_{i_p}$, which determine the words. (Starting from $(0, 0)$, as in the sketch of Haase and Halfon, words differing in leading zeros get the same value: the one-pair instance $u_1 = 01$, $v_1 = 1$ has no solution, yet both counters reach $1$.) Leaving $q_0$, a letter $\#$ subtracts $(1, 1)$ in a loop, so $q_f(0, 0)$ is reachable from $q_0(1, 1)$, after at least one round, exactly when the instance has a solution. Clause 2 follows from a lemma of the source that turns reachability in dimension $d$ into coverability in dimension $2d$, applied with $d = 2$. A good expansion links a page for that reduction from reachability to coverability.

## Sources

- Christoph Haase and Simon Halfon, *Integer Vector Addition Systems with States*, Reachability Problems (RP 2014), Lecture Notes in Computer Science 8762, Springer, 2014, pp. 112–124, https://doi.org/10.1007/978-3-319-11439-2_9; the definition of integer register machines and their decision problems, and the undecidability lemma for diagonal matrices with its proof in the appendix, read in arXiv:1406.2590v2. Locators in arXiv:1406.2590v2: Lemma 4 and its restatement as Lemma 15 with the proof in the appendix.
- Michael Blondin, Christoph Haase, Filip Mazowiecki and Mikhail Raskin, *Affine Extensions of Integer Vector Addition Systems with States*, Logical Methods in Computer Science 17(3), article 1, 2021, https://doi.org/10.46298/lmcs-17(3:1)2021; read as arXiv:1909.12386v3, which carries the journal's pagination: the proof of Proposition 6.3 (Reichert's reduction from the Post correspondence problem over $\{0, 1\}$ with the matrices $I$, $D_1 = \mathrm{diag}(2, 1)$, $D_2 = \mathrm{diag}(1, 2)$ and an artificial leading $1$), for clause 1.
