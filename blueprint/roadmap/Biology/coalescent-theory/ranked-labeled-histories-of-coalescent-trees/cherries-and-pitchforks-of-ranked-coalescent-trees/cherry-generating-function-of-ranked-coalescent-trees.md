# Cherry distribution of ranked coalescent trees via a weighted generating function

**Setting.** A *ranked tree* of size $n$ is an unlabeled rooted binary tree with $n$ leaves whose $n-1$ internal nodes are totally ordered in time (a ranked tree shape). Under the Kingman coalescent (equivalently the Yule process) a ranked tree $t$ with $o(t)$ cherries (internal nodes with two leaf children) has probability

$$P(t)=\frac{2^{\,n-1-o(t)}}{(n-1)!}.$$

**Theorem.**

*(1)* The weighted generating function $F(x,z)=\sum_{t}P(t)\,x^{o(t)}z^{n(t)}$, summed over ranked trees of size $n(t)>1$, is

$$F(x,z)=\frac{zx\,e^{2z\sqrt{1-x}}-zx}{\bigl(\sqrt{1-x}-1\bigr)e^{2z\sqrt{1-x}}+1+\sqrt{1-x}},$$

so $P_n(o=k)=[x^kz^n]F(x,z)$.

*(2)* *(Moments.)* The number of cherries $o$ of a coalescent ranked tree of size $n$ has

$$\mathbb E\,o=\frac n3\quad(n>2),\qquad \operatorname{Var}o=\frac{2n}{45}\quad(n>6).$$

*(3)* *(Coincidence probability.)* The probability that two independent coalescent ranked trees of size $n$ are identical is $p_n=\sum_tP(t)^2=\frac{4^{n-1}}{(n-1)!^2}\sum_t4^{-o(t)}$, which the same generating function evaluates as $p_2=p_3=1$, $p_4=\tfrac59$, $p_5=\tfrac29$, $p_6=\tfrac{16}{225}$.

*(4)* *(Pitchforks.)* Marking pitchforks (internal nodes whose children are a leaf and a cherry) by $v$, the trivariate generating function $Y_m(x,v,z)$ of $0$-$1$-$2$ increasing trees with $m$ nodes satisfies $Y_1=xz$ and

$$Y_{m+1}=\int\Bigl[(v+x)(1-v)\partial_vY_m+xY_m+x(v-2x)\partial_xY_m+xz\,\partial_zY_m\Bigr]dz,$$

which gives the joint law of cherries and pitchforks and the conditional law of pitchforks given cherries in closed form for each fixed size.

## Depends on

- [Ranked labeled history](../ranked-history.md)
- [Random joining](../random-joining.md)

## Expansion

Ranked trees are in bijection with $0$-$1$-$2$ increasing trees (label internal nodes by rank, leaves contribute outdegree-zero nodes); the coalescent weight depends on the tree only through its cherries, so a single variable $x$ marking cherries turns the weight into a substitution $Y_w(x,z)=Y(x/2,2z)$ in the exponential generating function $Y$ of increasing trees by outdegree. That $Y$ solves a Riccati-type differential equation in $z$, whose explicit solution gives the closed form for $F$. Differentiating in $x$ at $x=1$ yields $z^n/(3(z-1)^2)=n/3$ and the second factorial moment, hence the variance $2n/45$, recovering the classical Yule-model results by a purely enumerative route.

## Sources

- Filippo Disanto and Thomas Wiehe, *Exact enumeration of cherries and pitchforks in ranked trees under the coalescent model*, Math. Biosci. 242(2) (2013), 195–200. <https://doi.org/10.1016/j.mbs.2013.01.010> Section 2 (coalescent probability of ranked trees and the identical-tree probability proposition), the cherry generating-function proposition with its expectation and variance computations, and Section 3 (pitchfork recursion and Proposition 3). Locators use the numbering of the preprint arXiv:1112.1295.
