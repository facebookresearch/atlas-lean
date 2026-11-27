# First-order nilpotent minimum logic over NM-chains

Nilpotent minimum logic is the many-valued logic of the nilpotent minimum t-norm, an involutive extension of the monoidal t-norm based logic. Its first-order tautologies over a chain of truth values are the formulas taking value $1$ in every safe first-order model over that chain.

**NM-chains.** An *MTL-algebra* $(A, *, \Rightarrow, \sqcap, \sqcup, 0, 1)$ is a bounded lattice with a commutative monoid $(A, *, 1)$ residuated by $\Rightarrow$ ($z * x \leq y$ iff $z \leq x \Rightarrow y$) and satisfying prelinearity $(x \Rightarrow y) \sqcup (y \Rightarrow x) = 1$. An *NM-algebra* also satisfies ${\sim}{\sim}x = x$ and ${\sim}(x * y) \sqcup ((x \sqcap y) \Rightarrow (x * y)) = 1$, where ${\sim}x = x \Rightarrow 0$. In a totally ordered NM-algebra (an *NM-chain*) with strong negation $n(x) = {\sim}x$,

$$
x * y = \begin{cases} 0 & \text{if } x \leq n(y), \\ \min(x,y) & \text{otherwise,} \end{cases} \qquad x \Rightarrow y = \begin{cases} 1 & \text{if } x \leq y, \\ \max(n(x), y) & \text{otherwise.} \end{cases}
$$

$[0,1]_{\mathrm{NM}}$ is the chain on $[0,1]$ with $n(x) = 1 - x$; its subalgebras include $NM_\infty$ on $\{1/n\} \cup \{1 - 1/n\}$ ($n \geq 1$), $NM_\infty^-$, which is $NM_\infty$ without $1/2$, and $NM'_\infty$ on $\{1/2 - 1/(2n)\} \cup \{1/2 + 1/(2n)\} \cup \{1/2\}$. An element $x$ with $n(x) = x$ is a *negation fixpoint*.

**First-order semantics.** Formulas are first-order formulas over a fixed signature of predicate and constant symbols with the connectives $\&$, $\wedge$, $\to$, $\bot$ and the quantifiers. For a chain $\mathcal{A}$, an $\mathcal{A}$-model consists of a nonempty domain $M$, elements for the constants and maps $r_P : M^n \to A$ for the $n$-ary predicates; connectives are evaluated by the operations of $\mathcal{A}$, $\forall$ by infima and $\exists$ by suprema. A model is *safe* if all needed infima and suprema exist (always so if $\mathcal{A}$ is complete as a lattice). $\mathrm{TAUT}_{\mathcal{A}}\forall$ is the set of formulas whose value, the infimum over all evaluations of the variables, is $1$ in every safe $\mathcal{A}$-model; $\mathrm{monTAUT}_{\mathcal{A}}\forall$ is its restriction to monadic formulas (unary predicates only, no function or constant symbols).

## Depends on

- [Complete lattice](../../../Order/lattices-boolean-algebras/complete-lattice.md)

## Proof depends on

None.

## Expansion

Nilpotent minimum logic NM was introduced by Esteva and Godo; it is axiomatized by MTL with involution $\neg\neg\varphi \to \varphi$ and the weak nilpotent minimum axiom. Every infinite NM-chain with a negation fixpoint generates the variety of NM-algebras, while infinite chains without a fixpoint generate a different variety $\mathrm{NM}^-$, so at the propositional level there are exactly two infinite-valued nilpotent minimum logics.

## Sources

- M. Bianchi, "First-order nilpotent minimum logics: first steps", *Archive for Mathematical Logic* 52(3–4):295–316, 2013, doi:10.1007/s00153-012-0317-4; read as arXiv:1103.6025v2, <https://arxiv.org/abs/1103.6025v2>: Section 2 (syntax, MTL- and NM-algebras, the chains $NM_\infty$, $NM_\infty^-$, $NM'_\infty$, $[0,1]_{\mathrm{NM}}$, first-order models and safe models) and the beginning of Section 3 of arXiv:1103.6025v2.
