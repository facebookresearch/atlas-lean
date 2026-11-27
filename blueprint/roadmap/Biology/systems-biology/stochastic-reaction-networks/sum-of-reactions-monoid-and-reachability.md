# Sum of reactions monoid and reachability in stochastic reaction networks

**Setting.** Represent a reaction $y\to y'$ on $n$ species by the pair $r=(y,y')\in\mathbb{N}_0^n\times\mathbb{N}_0^n$ (reactant, product). For $x,y\in\mathbb{Z}^n$ write $x\le y$ componentwise and $x\vee y$ for the componentwise maximum. The **sum** of $r_1=(y_1,y_1')$ and $r_2=(y_2,y_2')$ is

$$r_1\oplus r_2=(y,y'),\qquad y=y_1+0\vee(y_2-y_1'),\qquad y'=y_2'+0\vee(y_1'-y_2),$$

the overall reaction obtained by firing $r_1$ and then $r_2$: species produced by $r_1$ and consumed by $r_2$ cancel, and only the deficit must be supplied in advance.

**Algebraic structure.**

- $(\mathbb{N}_0^n\times\mathbb{N}_0^n,\oplus)$ is a non-commutative monoid with identity $(0,0)$.
- The net gain is additive: $y'-y=(y_1'-y_1)+(y_2'-y_2)$, and for $x\in\mathbb{N}_0^n$, $x\ge y$ iff $x\ge y_1$ and $x+(y_1'-y_1)\ge y_2$. These two properties characterize $\oplus$ uniquely.
- With $r_1\sim r_2$ iff $y_1'-y_1=y_2'-y_2$ (same net gain), the quotient $((\mathbb{N}_0^n\times\mathbb{N}_0^n)/\sim,\oplus)$ is a commutative group.
- The inverse $r^{-1}=(y',y)$ satisfies $r\oplus r^{-1}=(y,y)$ and $(\oplus_{i=1}^m r_i)^{-1}=\oplus_{i=1}^m r_{m+1-i}^{-1}$.

**Reachability.** Let $\mathcal{R}$ be a reaction network modeled as a continuous-time Markov chain on $\mathbb{N}_0^n$ whose intensities satisfy $\lambda_{y\to y'}(x)>0\iff x\ge y$. Let $\mathrm{cl}(\mathcal{R})$ be the set of all finite $\oplus$-sums of reactions of $\mathcal{R}$, including $(0,0)$.

1. An ordered sequence of reactions $r_1,\dots,r_m\in\mathcal{R}$ can fire in succession from state $x$ iff $x\ge y$, where $(y,y')=\oplus_{i=1}^m r_i$.
2. A state $x$ leads to $x'$ iff there is $(y,y')\in\mathrm{cl}(\mathcal{R})$ with $x\ge y$ and $x'=x+y'-y$.
3. If two networks satisfy $\mathrm{cl}(\mathcal{R}_1)=\mathrm{cl}(\mathcal{R}_2)$, they have the same reachable set from every state. When no reaction has a catalytic species (no species appearing with positive coefficient on both sides of a reaction), the converse also holds.
4. Call $\mathcal{R}$ *essential* if $\mathrm{cl}(\mathcal{R})$ is closed under $r\mapsto r^{-1}$. Then $\mathcal{R}$ is essential iff, for all $x,x'\in\mathbb{N}_0^n$, $x$ leads to $x'$ implies $x'$ leads to $x$. In particular, reversible implies weakly reversible implies essential.
5. $\mathrm{cl}(\mathcal{R})$ need not be a semi-linear subset of $\mathbb{N}_0^{2n}$.

## Depends on

- [Weakly reversible reaction network](../../../Dynamics/smooth-dynamics/is-weakly-reversible.md)
- [Reversible networks are weakly reversible](../complex-balancing-and-the-deficiency-zero-theore/is-weakly-reversible-of-reversible.md)

## Expansion

Associativity is checked one coordinate at a time by splitting into the cases $y_2\ge y_1'$; $y_2<y_1'$ with $y_3\ge y_2'$; and $y_2<y_1'$ with $y_3<y_2'$. The identity $y=y_1\vee(y_1+y_2-y_1')$ shows that $x\ge y$ is exactly the condition for both reactions to fire in order, and induction gives the multi-step version. So reachability questions for the chain reduce to membership in the closure. Without catalytic species, every reaction with the net gain of $r_0\in\mathcal{R}_1$ dominates $r_0$ componentwise. The reaction realizing $y_0\to y_0'$ in $\mathcal{R}_2$ must therefore equal $r_0$, which gives the converse. For essentiality, a componentwise-minimal element of each net-gain class in $\mathrm{cl}(\mathcal{R})$ has its inverse in the closure, and $r_0^{-1}=r_*^{-1}\oplus r_0\oplus r_*^{-1}$ finishes the argument. The single gene-expression network $0\rightleftharpoons R$, $R\to R+P$, $P\to 0$ shows how this works: the sum $(0\to R)\oplus(R\to R+P)\oplus(R\to 0)$ equals $0\to P$, so every state of $\mathbb{N}_0^2$ is reachable from every other.

## Sources

- Linard Hoessly, Carsten Wiuf and Panqiu Xia, "On the sum of chemical reactions", European Journal of Applied Mathematics 34 (2023), 303–325, <https://doi.org/10.1017/s0956792522000146>; numbering as in arXiv:2105.04353: Definition 2.1, Propositions 2.2 and 2.4, Theorem 2.6, Definition 2.9, Lemma 2.10, Corollary 3.2, Lemma 3.3, Corollary 3.4, the theorem on networks without catalytic species (Section 3), Proposition 3.6, and the non-semi-linearity example (Section 3).
