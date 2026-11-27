# Demi-bits generators against a parity-closed proof system yield proof complexity generators

For a proof system closed under simple parity reductions, a demi-bits generator against that system, composed with a linear strong extractor under a suitable seed, becomes a proof complexity generator against it: average-case hardness of "$b\notin\mathrm{Range}(G)$" turns into hardness for every $b$.

**The formulas $\tau_b(G)$.** Let $G:\{0,1\}^n\to\{0,1\}^\ell$ ($\ell>n$) be a circuit of fan-in-2 gates over a basis containing $\oplus$, with $s$ internal gates (output gates included). For $b\in\{0,1\}^\ell$, the 3-CNF $\tau_b(G)$ has variables $x\in\{0,1\}^n$ and $\mathsf{hist}\in\{0,1\}^s$; for every internal gate $g$ with operation $\circ_g$ and children $g_l,g_r$ it contains the clauses of the constraint $v_g=v_{g_l}\circ_g v_{g_r}$, and for every output gate $g_i$ ($i\in[\ell]$) the unit clause of $v_{g_i}=b_i$. It is unsatisfiable exactly when $b\notin\mathrm{Range}(G)$.

**Simple parity reductions.** For CNFs $F(x_1,\dots,x_n)$ and $H(y_1,\dots,y_m)$, a simple parity reduction $F\le^\oplus H$ is a $\mathrm{GF}(2)$-linear map $\mathsf{redu}:\{0,1\}^n\to\{0,1\}^m$ such that for every clause $g$ of $H$, either $g\circ\mathsf{redu}\equiv\mathsf{True}$, or $g\circ\mathsf{redu}$ is an axiom of $F$, or $g$ is a width-1 clause and $g\circ\mathsf{redu}$ is the XOR of a subset of (necessarily width-1) axioms of $F$. A proof system $\mathcal P$ is closed under simple parity reductions if for some polynomial $p$, whenever $F\le^\oplus H$ and $H$ has a $\mathcal P$-proof of length $\ell$, $F$ has a $\mathcal P$-proof of length $p(\ell)$.

**Theorem.** Let $\mathcal P$ be a proof system closed under simple parity reductions.

1. If there exists a demi-bits generator $G:\{0,1\}^n\to\{0,1\}^{10n}$ secure against $\mathcal P$, then there is a (non-uniform) proof complexity generator secure against $\mathcal P$.
2. More precisely, let $G:\{0,1\}^n\to\{0,1\}^N$ be a demi-bits generator secure against $\mathcal P$, and let $\mathrm{Ext}:\{0,1\}^N\times\{0,1\}^d\to\{0,1\}^m$ be an $(N-2,2^{-m-1})$-strong linear seeded extractor, meaning that $\mathrm{Ext}(\cdot,r)$ is $\mathrm{GF}(2)$-linear for every seed $r$. Then there is a non-uniform proof complexity generator secure against $\mathcal P$, namely $C_r(s)=\mathrm{Ext}(G(s),r)$ for a suitable seed $r\in\{0,1\}^d$.

Resolution over linear equations modulo 2, $\mathrm{Res}[\oplus]$, is closed under simple parity reductions: if $F\le^\oplus H$ and $H$ has an $s$-step $\mathrm{Res}[\oplus]$ refutation, then $F$ has one with $2nm'+s$ steps, where $n$ is the number of variables of $F$ and $m'$ the number of clauses of $H$.

## Expansion

For linear $\mathrm{Ext}$, every $y\in\{0,1\}^N$ and seed $r$ give a simple parity reduction from $\tau_y(G)$ to $\tau_z(C_r)$ with $z=\mathrm{Ext}(y,r)$: the gates of $\mathrm{Ext}(\cdot,r)$ are XORs of output variables of $G$, internal-gate clauses of $G$ map to themselves, extractor-gate clauses become trivially true, and each output unit clause of $C_r$ becomes an XOR of output unit clauses of $\tau_y(G)$.

Suppose every $C_r$ fails, so each $r$ has a $z(r)$ with a short $\mathcal P$-proof of $\tau_{z(r)}(C_r)$. The test "$\tau_z(C_r)$ has a short proof" then accepts a random pair $(r,z)$ with probability at least $2^{-m}$, and the extractor property gives, for at least $3/4$ of all $y$, a seed $r$ for which $\tau_{\mathrm{Ext}(y,r)}(C_r)$ has a short proof. Closure under the reduction yields short proofs of $\tau_y(G)$ for those $y$, contradicting the demi-bits hardness of $G$. The argument is an average-case to best-case reduction that uses only nondeterminism.

In the same paper, demi-bits generators $G:\{0,1\}^n\to\{0,1\}^{100km}$ secure against $\mathsf{NP}/\mathrm{poly}$ give, for every non-uniform proof system, generators $\{0,1\}^n\to\{0,1\}^m$ that are $k$-round pseudo-surjective, the strongest hardness notion considered for proof complexity generators. The closure hypothesis excludes resolution, which is not closed under simple parity reductions; the restriction-based version of this transformation needs only monotonicity under adding axioms.

## Depends on

- [Demi-bits generators](demi-bits-generator.md)
- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Hanlin Ren, Yichuan Wang, Yan Zhong, "Hardness of Range Avoidance and Proof Complexity Generators from Demi-Bits", *ITCS* 2026, arXiv:2511.14061v2, https://arxiv.org/abs/2511.14061 (Theorems 1.4 and 3.5, Definition 3.3, Claim 3.4, Section 3.1, Theorem C.1, Theorem 1.7).
- Xin Li, Hanlin Ren, Yan Zhong, "Many Proof Complexity Generators Inside One Demi-Bits Generator", *FOCS* 2026, arXiv:2609.23228v1, https://arxiv.org/abs/2609.23228 (Remark 4.13).
