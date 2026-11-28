# Delta-products of modal logics

The δ-product of two unimodal logics is the logic of all product frames of their frames enriched with a diagonal constant δ, true exactly at the pairs $(x,x)$. It approximates two-variable first-order logic with equality and extends this approach to arbitrary component logics.

**Formulas.** Formulas are built from an infinite set of propositional variables and the constant $\delta$ with $\neg$, $\wedge$ and two boxes $\Box_h$ ("horizontal") and $\Box_v$ ("vertical"); $\Diamond_i = \neg\Box_i\neg$.

**Product and δ-product frames.** For unimodal Kripke frames $\mathfrak{F}_h = (W_h, R_h)$ and $\mathfrak{F}_v = (W_v, R_v)$, the product frame $\mathfrak{F}_h \times \mathfrak{F}_v$ is the binary case of the [product of frames](products-and-commutators-of-modal-logics.md), with $\overline{R}_h$ acting in the first coordinate and $\overline{R}_v$ in the second. The *δ-product* $\mathfrak{F}_h \times^\delta \mathfrak{F}_v$ adds the set $D = \{(x,x) : x \in W_h \cap W_v\}$, and $\delta$ is true at a point iff the point lies in $D$. A formula is valid in a frame if it is true at every point under every valuation.

**δ-product logics.** For a set $L$ of formulas, $\mathrm{Fr}\,L$ is the class of frames in which every formula of $L$ is valid, and $L$ is a *Kripke complete logic* if it is the set of formulas valid in every frame of some class of frames. For Kripke complete unimodal logics $L_h$, $L_v$,

$$
L_h \times^\delta L_v = \{\varphi : \varphi \text{ is valid in } \mathfrak{F}_h \times^\delta \mathfrak{F}_v \text{ for all } \mathfrak{F}_h \in \mathrm{Fr}\,L_h,\ \mathfrak{F}_v \in \mathrm{Fr}\,L_v\},
$$

and for classes $\mathcal{C}_h$, $\mathcal{C}_v$ of frames, $\mathrm{Log}(\mathcal{C}_h \times^\delta \mathcal{C}_v)$ is the set of formulas valid in every $\mathfrak{F}_h \times^\delta \mathfrak{F}_v$ with $\mathfrak{F}_h \in \mathcal{C}_h$ and $\mathfrak{F}_v \in \mathcal{C}_v$. A logic $L$ is *decidable* if its validity problem (given $\varphi$, is $\varphi \in L$?) is decidable.

**Frames used in the undecidability results.** For $0 < k \leq \omega$, a *$k$-fan* is any frame $(k, R)$, with $k = \{0, 1, \dots\}$ the set of naturals below $k$, such that $(0,n) \in R$ for all $0 < n < k$. For $k \leq \omega$, $\mathfrak{H}_k = (k+1, S_k)$ with $S_k = \{(k,n) : n < k\} \cup \{(n-1,n) : 0 < n < k\}$ is the successor frame on $k$ with an added "spy point" $k$.

## Depends on

- [Kripke model](../../kripke-semantics/kripke-model.md)
- [Modal formulas](../../kripke-semantics/formula.md)
- [Products and commutators of modal logics](products-and-commutators-of-modal-logics.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

δ-products approximate two-variable first-order logic with equality: $\Box_h$ and $\Box_v$ act as $\forall x$ and $\forall y$, and $\delta$ as $x = y$. The transposition-free two-variable fragment corresponds exactly to the variant $\mathbf{S5} \times^\delta_{sq} \mathbf{S5}$, the logic of δ-products of rooted frames with equal universes; $\mathbf{S5} \times^\delta \mathbf{S5}$ is properly contained in it (it does not contain $\Diamond_h \delta$). Every result of the source stated for $L_h \times^\delta L_v$ also holds for the corresponding variant $L_h \times^\delta_{sq} L_v$. If $\mathrm{Fr}\,L_h$ and $\mathrm{Fr}\,L_v$ are recursively first-order definable in the language with one binary predicate symbol, then $L_h \times^\delta L_v$ is recursively enumerable (Theorem 1).

## Sources

- Christopher Hampson, Stanislav Kikot and Agi Kurucz, "The decision problem of modal product logics with a diagonal, and faulty counter machines", *Studia Logica* 104(3):455–486, 2016, doi:10.1007/s11225-015-9647-7; read as arXiv:1509.02060v1, <https://arxiv.org/abs/1509.02060v1>: Section 2 (formulas, δ-frames, products, δ-products and the decision problems), Theorem 1 in Section 3, the definition of $k$-fans at the start of Section 5, and the frames $\mathfrak{H}_k$ before Theorem 3 of arXiv:1509.02060v1.
