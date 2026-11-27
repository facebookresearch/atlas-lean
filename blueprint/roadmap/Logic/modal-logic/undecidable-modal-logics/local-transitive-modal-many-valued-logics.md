# Local consequence in transitive modal many-valued logics is undecidable

Local consequence over transitive Kripke models whose formulas take values in algebras such as the standard Łukasiewicz or product algebra is undecidable, already for three-variable formulas and also over finite transitive models.

**Setting.** An FL$_{ew}$-algebra is a bounded commutative integral residuated lattice $(A, \wedge, \vee, \cdot, \to, 0, 1)$; it is *$n$-contractive* if $a^{n+1} = a^n$ for all $a \in A$. Let $\mathsf{A}$ be a class of weakly archimedean linearly ordered FL$_{ew}$-algebras such that for every $n \in \omega$ some member of $\mathsf{A}$ is not $n$-contractive; examples are $\{[0,1]_{\text{Ł}}\}$ (the standard MV-algebra), $\{\mathrm{MV}_n : n \in \omega\}$, $\{[0,1]_\Pi\}$ (the standard product algebra) and the one-generated subalgebras of $[0,1]_\Pi$, but not the standard Gödel algebra. Modal formulas are built from variables and constants with $\wedge, \vee, \cdot, \to$ and unary $\Box$, $\Diamond$. An $\mathbf{A}$-Kripke model, for $\mathbf{A} \in \mathsf{A}$, is a [Kripke frame](../kripke-semantics/kripke-model.md) $(W, R)$ with a crisp accessibility relation and a valuation $e\colon W \times \mathrm{Var} \to A$ extended by $e(v, \Box\varphi) = \bigwedge_{Rvw} e(w, \varphi)$ and $e(v, \Diamond\varphi) = \bigvee_{Rvw} e(w, \varphi)$; it is *safe* when these infima and suprema exist. $4\mathcal{K}_{\mathsf{A}}$ is the class of safe transitive $\mathbf{A}$-Kripke models with $\mathbf{A} \in \mathsf{A}$, and $\omega 4\mathcal{K}_{\mathsf{A}}$ its finite members. For a finite set $\Gamma$ and a formula $\varphi$, $\varphi$ *follows locally* from $\Gamma$ in a class $\mathcal{C}$ if for every model in $\mathcal{C}$ and every world $v$, $e(v, \psi) = 1$ for all $\psi \in \Gamma$ implies $e(v, \varphi) = 1$.

**Theorem (Vidal).** For every such class $\mathsf{A}$, the problem of determining whether $\varphi$ follows locally from $\Gamma$ in $4\mathcal{K}_{\mathsf{A}}$ is undecidable, and so is the same problem in $\omega 4\mathcal{K}_{\mathsf{A}}$. Both remain undecidable for formulas in three variables (Theorem 3.1 of the source).

The source also shows that local consequence of modal Łukasiewicz logic over all Kripke models is decidable, so this logic is decidable while its transitive expansion is not. Global consequence over all frames is the subject of [a separate result](global-modal-many-valued-logics.md) of the same author.

## Depends on

- [Kripke model](../kripke-semantics/kripke-model.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

From an instance $P$ of the Post correspondence problem the proof computes a finite set $\Gamma_P$ and a formula $\varphi_P$ in the variables $y, v, w$ such that $P$ has a solution if and only if $\Box\varphi_P$ does not follow locally from $\Gamma_P$ in $4\mathcal{K}_{\mathsf{A}}$, equivalently in $\omega 4\mathcal{K}_{\mathsf{A}}$ (Proposition 3.9). Transitivity forces the value of $y$ to be constant on the successors of the root, and non-contractive elements encode the two words of a candidate solution as powers of that value along a finite chain of worlds.

## Sources

- Amanda Vidal, "On transitive modal many-valued logics", *Fuzzy Sets and Systems* 407:97–114, 2021, doi:[10.1016/j.fss.2020.01.011](https://doi.org/10.1016/j.fss.2020.01.011). Numbering of the version read, arXiv:1904.01407v1: Theorem 3.1, Proposition 3.9 and Sections 2 to 4.
