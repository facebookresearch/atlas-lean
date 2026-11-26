# Adaptive dynamics and the neutral center of the continuous voluntary public good game

**Game.** Each individual has two continuous traits $x=(c,p)\in[0,1]^2$: an investment level $c$ and a probability $p$ of joining a public good game. Groups of $N\ge2$ are drawn at random; each member participates with its own probability. Participants pay their investment, the total is multiplied by $r>1$ and shared equally among participants; non-participants (and a lone participant) receive a fixed payoff $\sigma$ with $0<\sigma<r-1$. Let

$$F(z)=1+(r-1)z^{N-1}-\frac{r(1-z^N)}{N(1-z)},\qquad c_Q=\frac{\sigma}{r-1}.$$

$F$ has the root $z=1$ and, for $r>2$, a unique interior root $z_Q\in(0,1)$.

**Invasion fitness.** For a rare mutant $y=(c_y,p_y)$ in a monomorphic resident $x=(c_x,p_x)$, with growth rate given by its payoff advantage, the invasion fitness is bilinear in the trait differences:

$$S(x,y)=a_{10}(x)(c_y-c_x)+a_{01}(x)(p_y-p_x)+a_{11}(x)(c_y-c_x)(p_y-p_x),$$

$$a_{10}=-p_xF(1-p_x),\qquad a_{01}=(r-1)(c_x-c_Q)\bigl(1-(1-p_x)^{N-1}\bigr),\qquad a_{11}=-F(1-p_x).$$

**Theorem (monomorphic adaptive dynamics).** The canonical equation $\dot x=D(x)=(a_{10}(x),a_{01}(x))$ reads

$$\dot c=-p\,F(1-p),\qquad \dot p=(r-1)(c-c_Q)\bigl(1-(1-p)^{N-1}\bigr).$$

Every orbit is symmetric about the line $c=c_Q$, and the boundary $p=0$ is a line of equilibria, Lyapunov stable for $c<c_Q$ and unstable for $c>c_Q$.

1. If $r\le2$, every orbit in $p>0$ leaves the boundary segment $\{c>c_Q\}$, circles counter-clockwise around $(c_Q,0)$ and converges to the segment $\{c<c_Q\}$: participation collapses.
2. If $r>2$, the point $Q=(c_Q,p_Q)$ with $p_Q=1-z_Q$ is a center surrounded by closed periodic orbits, so monomorphic populations oscillate in cooperation and participation without approaching $Q$. At $Q$ the invasion fitness vanishes identically, $S(Q,y)=0$ for all $y$; $Q$ and every point of $p=0$ are symmetric, non-strict Nash equilibria, and neither is a neighborhood invader strategy, so any mutant can invade $Q$ by neutral drift.

**Theorem (polymorphic populations).** For a population whose strategy distribution $X$ is centered at $Q$, the center is stable if and only if the covariance between investment and participation is negative, $\operatorname{Cov}(X)<0$; as long as this holds the strategy cloud keeps spreading by neutral drift, and when drift makes the covariance non-negative the cloud collapses, producing cycles of diversification and collapse.

## Depends on

- [Classification of adaptive-dynamics singular strategies](../classification-of-adaptive-dynamics-singular-str/README.md)

## Expansion

The mutant's expected payoff is affine in its participation probability, $P(x,y)=p_y\,g(x,y)+(1-p_y)\sigma$, where $g$ is its expected payoff when it participates; averaging over the binomial number of participating co-players gives the explicit bilinear form above, and $S(x,x)=0$. Dividing the vector field by $1-(1-p)^{N-1}>0$ (a time change on $p>0$) separates variables: $\dot p=(r-1)(c-c_Q)$ and $\dot c=-h(p)$ with $h(p)=pF(1-p)/(1-(1-p)^{N-1})$, so

$$H(c,p)=\frac{r-1}2(c-c_Q)^2+\int^p h(s)\,ds$$

is conserved. For $r>2$, $h$ changes sign at $p_Q=1-z_Q$, so $H$ has a strict local minimum at $Q$ and its level sets near $Q$ are closed curves, giving a center; for $r\le2$, $h$ has one sign on $(0,1]$ and orbits run between the two halves of the boundary. For a polymorphic population, expanding the bilinear invasion fitness around the mean strategy shows that the second-order term $a_{11}$ couples the traits through their covariance, which determines whether the representative strategy is pulled back to $Q$.

## Sources

- Tatsuya Sasaki, Åke Brännström, Isamu Okada, Tatsuo Unemi, "Unchecked strategy diversification and collapse in continuous voluntary public good games", arXiv (2015). Section 2 (model), Section 4.1 (invasion fitness, selection gradient, singular strategies), Section 4.3 (polymorphic populations and the covariance criterion), Appendix A. <https://doi.org/10.48550/arXiv.1502.03779>
