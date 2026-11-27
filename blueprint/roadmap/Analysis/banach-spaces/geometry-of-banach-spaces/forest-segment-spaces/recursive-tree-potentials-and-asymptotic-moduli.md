# Recursive tree-potential completions, midpoint estimates and renorming obstructions

For finitely supported real coordinates $v_s$ on a rooted tree, take the finite ancestor-closed head containing the support and the root. Compute two nonnegative fields $P_s,Q_s$ from the leaves upward: with $a,b$ the respective $\ell_p$ norms of the children's $P,Q$ values, use

$$(P_s,Q_s)=\big(\max(a,v_s+b),\max(b,-v_s+a)\big).$$

Extend by zero outside the head. The full word tree has all finite words over $\mathbb N$ as nodes. Its root is the empty word, its parent operation deletes the last letter (fixing the empty word), and its depth is word length. For each positive integer $h$, the height-$h$ tree restricts these operations to words of length at most $h$. The joined tree has a separate root of depth zero and nodes $(h,s)$ for each $h\ge1$ and each word $s$ of length at most $h$. On a tagged nonempty word the parent deletes the last letter and keeps the tag; the parent of a tagged empty word is the joined root, whose own parent is itself. The depth of $(h,s)$ is $1+|s|$.

Use $p=2$ for the following spaces: $X_\Sigma$ completes the full word tree with root norm $P+Q$; $X_J$ completes the joined tree, also in root norm $P+Q$; $X_0$ completes the vectors of the joined tree with coefficient zero at its separate root, in root norm $P=Q$. The lower, upper and midpoint moduli below use an infimum over unit centers, a supremum over closed finite-codimensional subspaces and an infimum over directions in those subspaces. For the averaged midpoint gain use directions of norm at least one and gain $(\|x+ty\|+\|x-ty\|)/2-1$; for the one-sided modulus in a norm $N$, use $N(y)=1$ and gain $N(x+ty)-1$. An equivalent norm has two-sided bounds $a\|x\|\le N(x)\le b\|x\|$ with $0<a\le b$, and is AUC if the one-sided modulus is positive at every $t>0$.

A single set of structural facts is asserted before all the conclusions below. Take any carrier with decidable equality and a rooted parent system: the parent fixes the root, the root has depth zero, and the natural depth strictly decreases on taking the parent of any nonroot node. The head of a finite vector is the root together with the finite ancestor closure of the support. The asserted facts are that heads are initial; the root-sum formula gives a real norm dominating each coordinate and making finite initial-head projections contractive; the root-zero formula gives a real norm equal to half the root-sum norm on that subspace; and for every real child exponent $p\ge1$ the variable-exponent root sum gives a real norm dominating each coordinate. The usual coordinate map on finite vectors has dense range in coordinate $\ell_p$ for every such $p$. For $p>1$, when depth increases by one along each child edge and depths are bounded by $h$, its two-sided norm comparison is the one for $\nu_h$ below with $p$ in place of $p_h$.

The three completions are complete and infinite-dimensional; $X_0$ and $X_J$ are canonically reflexive. Coordinates and both fields extend continuously, agree with their values on finite vectors, and obey the respective root norm formulas, with root coordinate zero on $X_0$. On each of the three spaces, retaining any finite ancestor-closed head containing the root is a contractive idempotent linear projection with finite-dimensional range and exactly the indicated coordinate action. The kernel is closed and finite codimensional, and finitely supported vectors with vanishing head are dense in this kernel.

- For $0<t<1$ both $X_\Sigma$ and $X_J$ have averaged midpoint modulus at least $t^3/128$; for every $t>0$ the modulus of $X_\Sigma$ is positive. In $X_0$, if $x$ has coordinates vanishing off a finite ancestor-closed head containing the root and $z\ne0$ has coordinates vanishing on it, then $(\|x+z\|+\|x-z\|)/2\ge\|x\|+\|z\|^3/[8(2\|x\|+\|z\|)^2]$. No equivalent norm on any of these three spaces is AUC.
- In $X_J$, for every $\epsilon>0$ there is $0<\eta<1$ such that for every $x\in X_J$ and every sequence $(z_i)_{i\in\mathbb N}$ in $X_J$, if $\|x\pm z_i\|\le1$ for each $i$ and $\|z_i-z_j\|\ge\epsilon$ for $i\ne j$, then $\|x\|\le1-\eta$. For $\epsilon\le2$, $\eta=\min(1/2,\gamma(2,\epsilon/16))$, where $u=\beta^2/(2M^2)$, $c=\beta\sqrt u/8$, $L=1+\log(M/c)$ and $\gamma(M,\beta)=\beta u\exp(-4(2+\sqrt6)L/u)/8$.

For the variable-exponent space, on the tree of height $h\ge1$ use $p_h=1+1/h$ in the same recursion and root norm $P+Q$. Complete to obtain $E_h$ and put $X_V=(\bigoplus_h E_h)_{\ell_2}$. The coordinate map identifies each $E_h$ with ordinary coordinate $\ell_{p_h}$ on its nodes; denote the transported norm by $\nu_h$. This is a genuine absolutely homogeneous norm with

$$(h+1)^{-1/p_h}\|v\|_{p_h}\le\nu_h(v)\le 2(h+1)^{1-1/p_h}\|v\|_{p_h}.$$

Each component and $X_V$ is complete and canonically reflexive, with separable continuous dual. In $X_V$, finitely supported coordinate vectors are dense, and each finite coordinate projection is continuous, finite rank and idempotent, retaining precisely those coordinates. In the exact recursion on ordinary $\ell_{p_h}$ coordinates, quantify over all real-valued pairs of fields $f=(f_1,f_2)$ on the height-$h$ tree. For either real field $g$, define

$$A_h(g,s)=\left(\sum_{c:\,c\text{ is a child of }s} g(c)^{p_h}\right)^{1/p_h}.$$

Child means a nonroot node whose parent is $s$. The sum is the totalized real series (zero if nonsummable). Both exponentiations use Mathlib's total real power: $x^a=\exp(a\log x)$ for $x>0$, $x^a=\exp(a\log(-x))\cos(\pi a)$ for $x<0$, and $0^a$ is $1$ if $a=0$ and $0$ otherwise. In particular there is **no** replacement by absolute values or restriction on the signs of $g(c)$ or of the series value before taking the outer power. For every $v\in\ell_{p_h}$, if $f(s)$ equals the displayed least pair at $v(s)$ with $a=A_h(f_1,s)$ and $b=A_h(f_2,s)$ at every node, then $f$ equals the two extended potential fields and their root sum is $\nu_h(v)$.

- Every equivalent norm $N$ on $X_V$ has one-sided modulus zero at $a/b$ for its given comparison constants $a,b$, hence is not AUC.
- Put $c_3=(6e)^{-3}$ and $c_6=2\exp(-(e-1))4^{-6}$. Suppose $x$ is finitely supported across all components, and for each component with $x_h\ne0$ a finite ancestor-closed head contains the support of $x_h$ and all the corresponding coordinates of $y_h$ vanish on it. The following inequality uses division by zero interpreted as zero. If also $R>0$ and $\|x\pm y\|\le R$, then $\|x\|^2+c_3\|y\|^3/(2\sqrt2 R)\le R^2$.

$$\frac{c_6\|y\|^6}{(\|x+y\|^2+\|x-y\|^2)^2}\le\|x+y\|^2+\|x-y\|^2-2\|x\|^2.$$

For weakly null sequences there is also the following consequence. If $0<\epsilon\le1$ and $(y_j)_{j\in\mathbb N}$ is weakly null in $X_V$ with $\epsilon\le\|y_j\|$ and $\|x\pm y_j\|\le1$ for all $j$, then $\|x\|\le\sqrt{1-c_3\epsilon^3/(2\sqrt2)}<1$.

## Depends on

- The head restriction and least-pair potential recursion, the completion and coordinate models and the exact norm/modulus conventions above.

## Proof depends on

- Existence of the five compatible structures for ancestor heads, root-sum normed vectors, root-zero normed vectors, variable-exponent normed vectors and the dense two-sided coordinate $\ell_p$ comparison.
- Completion and reflexivity identifications, the separate midpoint and renorming estimates, and the component-to-square-sum estimates for the variable-exponent space.

## Expansion

Develop the finite-support recursion and its five structural witnesses before the eleven jointly stated results. Split projection/density and reflexivity from midpoint and renorming assertions. Verify the exact infinite-child recursion and coordinate comparison before proving the sixth-order estimate, cubic lens estimate and weak-tail consequence with their distinct hypotheses.

## Sources

- OpenAI, [RecursivePotentials comparator, main](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RecursivePotentials.lean#L955-L957).
- OpenAI, [rooted parent systems](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RecursivePotentials.lean#L20-L26), [word-tree definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RecursivePotentials.lean#L105-L128), and [height-bounded word tree](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RecursivePotentials.lean#L212-L222).
- OpenAI, [arbitrary-field recursion and exactness](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RecursivePotentials.lean#L918-L933), using Mathlib's [total real powers](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean#L34-L51) and [negative and zero base formulas](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean#L94-L113).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/331.md).
